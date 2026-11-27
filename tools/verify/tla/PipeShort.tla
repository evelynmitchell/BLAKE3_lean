------------------------------- MODULE PipeShort -------------------------------
(* threads/src/pipeline.rs: short messages sharing a Room and groups, and
   small batches, from the commit to the event, and Pipeline::drop.

   A short commit (less than ROOM_LEN, commit) takes one of the held Room's
   credits (take_credit: a Room never gives out its last; at Credits - 1
   commits it takes a new set) and leaves the slot OpenShort, its bytes in
   the Room at the hand-out it was committed from. Several short messages
   share one Room. A message's end (end) or a wait for a Room
   (flush_sealed_short_rooms, for every OpenShort slot) makes it a member
   of the open group (push_member), its room in the group's metas
   (local_rooms); a group holds `Members` at most and is published full, or
   by a wait (publish_open). A small batch (batch, under TASK_LEN) is a
   member too, of a group of batches; its digests are the group's to write
   and the owner's to read at its event. A member of the other kind
   publishes the open group first. An abort gives an OpenShort slot's
   credit back at once; a sent-on one's comes back with its group.

   A group's task (run_group) hashes its members (reads their bytes, writes
   their outputs), gives back its members' credits, one subtraction a room
   (coalesced), then stores its epoch in completed_epoch. Groups are reused
   by epoch (acquire_free_group: the group at the cursor, once the epoch
   last assigned to it has completed; else the next, the owner spinning),
   and a member's event waits for its epoch (group_ready). A Room is free,
   and may be handed out again over the same bytes, once its count is 0;
   the owner's drop of the Room it holds gives back the credits it has left
   (Room::drop). Pipeline::drop, with no group in flight (otherwise the
   process stops: has_in_flight_work), gives back the credits of OpenShort
   slots and of the open group's members.

   `Credits` is 3, against 2^30 in the code (tools/verify/lean/Credits.lean
   has the count's arithmetic at size). The waits are abstract: a wait ends
   when what it waits for is so (the WakerSlot's contract, Waker.tla). *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Msgs, Rooms, Credits, Groups, Members

M == 1..Msgs
R == 1..Rooms
G == 1..Groups

VARIABLES refs, gen, held, commits,       \* each room's count and hand-outs; the Room held (0: none); its commits
          msg,                             \* each message: place, kind, room, hand-out, group, epoch
          back,                            \* each short message's credit given back, how many times
          grp, assigned, completed, wst,   \* each group: epoch, kind, members, metas; epoch assigned, completed; its task
          openG, nextE, cursor,            \* the open group (0: none); the next epoch; acquire_free_group's cursor
          out,                             \* each message's output written by its group
          opened, opc, dropped

vars == <<refs, gen, held, commits, msg, back, grp, assigned, completed, wst, openG, nextE, cursor, out, opened, opc, dropped>>
rooms == <<refs, gen, held, commits>>
groups == <<grp, assigned, completed, wst, openG, nextE, cursor>>

NoMsg == [pc |-> "new", kind |-> "none", r |-> 0, gen |-> 0, g |-> 0, e |-> 0]
Init == /\ refs = [r \in R |-> 0] /\ gen = [r \in R |-> 0] /\ held = 0 /\ commits = 0
        /\ msg = [m \in M |-> NoMsg] /\ back = [m \in M |-> 0]
        /\ grp = [g \in G |-> [epoch |-> 0, kind |-> "none", members |-> <<>>, metas |-> <<>>]]
        /\ assigned = [g \in G |-> 0] /\ completed = [g \in G |-> 0] /\ wst = [g \in G |-> "idle"]
        /\ openG = 0 /\ nextE = 1 /\ cursor = 1 /\ out = [m \in M |-> FALSE]
        /\ opened = 0 /\ opc = "idle" /\ dropped = FALSE

Free(r) == refs[r] = 0 /\ held # r
InFlight(g) == completed[g] < assigned[g]
Ready(m) == IF msg[m].g = 0 THEN TRUE ELSE completed[msg[m].g] >= msg[m].e
Active == opc = "idle" /\ ~dropped
Short(m) == msg[m].kind = "short"
\* A short message's credit is out: in its slot, or with its group, not yet back.
Out(m) == Short(m) /\ back[m] = 0 /\ msg[m].pc \notin {"new"}

InGroup(g) == {grp[g].members[i] : i \in 1..Len(grp[g].members)}

(* publish_open. *)
Publish == IF openG = 0 THEN UNCHANGED <<assigned, wst, openG>>
           ELSE /\ assigned' = [assigned EXCEPT ![openG] = grp[openG].epoch]
                /\ wst' = [wst EXCEPT ![openG] = "queued"] /\ openG' = 0

(* push_member for message m, of kind k, to place `next`: join the open
   group of its kind, publishing it full; or, none open of that kind, a
   step of acquire_free_group (publishing an open group of the other kind
   first). *)
CanJoin(k) == openG # 0 /\ grp[openG].kind = k
\* Join group g at epoch e, its members so far `ms` and metas `rs`.
JoinAt(m, next, g, e, k, ms, rs) ==
    LET full == Len(ms) + 1 = Members IN
    /\ grp' = [grp EXCEPT ![g] = [epoch |-> e, kind |-> k, members |-> Append(ms, m), metas |-> Append(rs, msg[m].r)]]
    /\ msg' = [msg EXCEPT ![m].pc = next, ![m].g = g, ![m].e = e]
    /\ IF full THEN assigned' = [assigned EXCEPT ![g] = e] /\ wst' = [wst EXCEPT ![g] = "queued"] /\ openG' = 0
       ELSE openG' = g /\ UNCHANGED <<assigned, wst>>
Push(m, k, next) ==
    IF CanJoin(k)
    THEN JoinAt(m, next, openG, grp[openG].epoch, k, grp[openG].members, grp[openG].metas) /\ UNCHANGED <<completed, nextE, cursor>>
    ELSE IF openG # 0
    THEN Publish /\ UNCHANGED <<grp, msg, completed, nextE, cursor>>
    ELSE LET g == cursor IN       \* open_new_group, and the member pushed
         /\ cursor' = (g % Groups) + 1
         /\ IF ~InFlight(g)
            THEN JoinAt(m, next, g, nextE, k, <<>>, <<>>) /\ nextE' = nextE + 1
            ELSE UNCHANGED <<grp, msg, assigned, wst, openG, nextE>>
         /\ UNCHANGED completed

(* The owner. *)
\* room(): a free room, given all its credits.
TakeRoom == /\ Active /\ held = 0 /\ opened < Msgs
            /\ \E r \in R : /\ Free(r) /\ gen[r] < Msgs
                            /\ held' = r /\ refs' = [refs EXCEPT ![r] = Credits] /\ gen' = [gen EXCEPT ![r] = @ + 1]
            /\ commits' = 0
            /\ UNCHANGED <<msg, back, groups, out, opened, opc, dropped>>
\* room() with none free: send every short Room on, publish (poll_room),
\* and wait for one to be free.
RoomWait == /\ Active /\ held = 0 /\ opened < Msgs /\ \A r \in R : ~Free(r)
            /\ opc' = "flush" /\ UNCHANGED <<rooms, msg, back, groups, out, opened, dropped>>
Flush == /\ opc = "flush"
         /\ IF \E m \in M : msg[m].pc = "openshort"
            THEN \E m \in M : msg[m].pc = "openshort" /\ Push(m, "short", "dispatched") /\ UNCHANGED opc
            ELSE Publish /\ opc' = "roomwait" /\ UNCHANGED <<grp, msg, completed, nextE, cursor>>
         /\ UNCHANGED <<rooms, back, out, opened, dropped>>
RoomWake == /\ opc = "roomwait" /\ \E r \in R : Free(r)
            /\ opc' = "idle" /\ UNCHANGED <<rooms, msg, back, groups, out, opened, dropped>>
\* Room::drop: the credits the Room has left.
DropRoom == /\ opc = "idle" /\ held # 0
            /\ refs' = [refs EXCEPT ![held] = @ - (Credits - commits)] /\ held' = 0 /\ commits' = 0
            /\ UNCHANGED <<gen, msg, back, groups, out, opened, opc, dropped>>
\* A short commit: a new message, one credit of the held Room.
Commit == /\ Active /\ held # 0 /\ opened < Msgs
          /\ LET m == opened + 1  renew == commits = Credits - 1 IN
             /\ refs' = IF renew THEN [refs EXCEPT ![held] = @ + (Credits - 1)] ELSE refs
             /\ commits' = (IF renew THEN 0 ELSE commits) + 1
             /\ msg' = [msg EXCEPT ![m] = [NoMsg EXCEPT !.pc = "openshort", !.kind = "short", !.r = held, !.gen = gen[held]]]
          /\ opened' = opened + 1
          /\ UNCHANGED <<gen, held, back, groups, out, opc, dropped>>
\* A small batch: a new message, made a member.
Batch == /\ Active /\ opened < Msgs
         /\ msg' = [msg EXCEPT ![opened + 1] = [NoMsg EXCEPT !.pc = "batching", !.kind = "batch"]]
         /\ opened' = opened + 1
         /\ UNCHANGED <<rooms, back, groups, out, opc, dropped>>
OnMsg(m) ==
    /\ Active
    /\ \/ msg[m].pc = "batching" /\ Push(m, "batch", "wait")
       \/ msg[m].pc = "openshort" /\ Push(m, "short", "wait")                        \* end
       \/ msg[m].pc = "dispatched" /\ msg' = [msg EXCEPT ![m].pc = "wait"] /\ UNCHANGED <<grp, assigned, completed, wst, openG, nextE, cursor>>
       \/ msg[m].pc = "dispatched" /\ msg' = [msg EXCEPT ![m].pc = "aborted"] /\ UNCHANGED <<grp, assigned, completed, wst, openG, nextE, cursor>>
    /\ UNCHANGED <<rooms, back, out, opened, opc, dropped>>
\* abort of an OpenShort slot: its credit back now.
AbortShort(m) == /\ Active /\ msg[m].pc = "openshort"
                 /\ refs' = [refs EXCEPT ![msg[m].r] = @ - 1] /\ back' = [back EXCEPT ![m] = @ + 1]
                 /\ msg' = [msg EXCEPT ![m].pc = "aborted"]
                 /\ UNCHANGED <<gen, held, commits, groups, out, opened, opc, dropped>>
\* A wait for events publishes the open group (ready's front_uses_open_group).
PublishOpen == /\ Active /\ openG # 0 /\ Publish
               /\ UNCHANGED <<rooms, msg, back, grp, completed, nextE, cursor, out, opened, opc, dropped>>
\* An event, its group's epoch complete (group_ready): a short's hash or a
\* batch's digests read out.
Event(m) == /\ Active /\ msg[m].pc \in {"wait", "aborted"} /\ Ready(m)
            /\ msg' = [msg EXCEPT ![m].pc = "taken"]
            /\ UNCHANGED <<rooms, back, groups, out, opened, opc, dropped>>
\* Pipeline::drop, with no group in flight.
DropPipeline ==
    /\ Active /\ \A g \in G : ~InFlight(g)
    /\ LET gone == {m \in M : msg[m].pc = "openshort" \/ (Short(m) /\ openG # 0 /\ m \in InGroup(openG))}
       IN /\ refs' = [r \in R |-> refs[r] - Cardinality({m \in gone : msg[m].r = r})]
          /\ back' = [m \in M |-> IF m \in gone THEN back[m] + 1 ELSE back[m]]
    /\ dropped' = TRUE /\ openG' = 0
    /\ UNCHANGED <<gen, held, commits, msg, grp, assigned, completed, wst, nextE, cursor, out, opened, opc>>
\* The Room held may be dropped after its Pipeline (PipeStorage.tla has the
\* closing bit that then frees the storage).
DropRoomAfter == dropped /\ DropRoom

Owner == TakeRoom \/ RoomWait \/ Flush \/ RoomWake \/ (~dropped /\ DropRoom) \/ Commit \/ Batch
         \/ (\E m \in M : OnMsg(m) \/ AbortShort(m) \/ Event(m)) \/ PublishOpen \/ DropPipeline \/ DropRoomAfter

(* A group's task: hash (read the members' bytes, write their outputs);
   give back the credits, one room a step; complete its epoch. *)
Hash(g) == /\ wst[g] = "queued"
           /\ out' = [m \in M |-> m \in InGroup(g) \/ out[m]]
           /\ wst' = [wst EXCEPT ![g] = "release"]
           /\ UNCHANGED <<rooms, msg, back, grp, assigned, completed, openG, nextE, cursor, opened, opc, dropped>>
Left(g) == {grp[g].metas[i] : i \in 1..Len(grp[g].metas)} \ {0}
Release(g) == /\ wst[g] = "release" /\ Left(g) # {}
              /\ \E r \in Left(g) :
                   LET ix == {i \in 1..Len(grp[g].metas) : grp[g].metas[i] = r}
                       ms == {grp[g].members[i] : i \in ix}
                   IN /\ refs' = [refs EXCEPT ![r] = @ - Cardinality(ix)]
                      /\ back' = [m \in M |-> IF m \in ms THEN back[m] + 1 ELSE back[m]]
                      /\ grp' = [grp EXCEPT ![g].metas = [i \in 1..Len(grp[g].metas) |-> IF i \in ix THEN 0 ELSE grp[g].metas[i]]]
              /\ UNCHANGED <<gen, held, commits, msg, assigned, completed, wst, openG, nextE, cursor, out, opened, opc, dropped>>
Complete(g) == /\ wst[g] = "release" /\ Left(g) = {}
               /\ completed' = [completed EXCEPT ![g] = grp[g].epoch] /\ wst' = [wst EXCEPT ![g] = "idle"]
               /\ UNCHANGED <<rooms, msg, back, grp, assigned, openG, nextE, cursor, out, opened, opc, dropped>>
Worker(g) == Hash(g) \/ Release(g) \/ Complete(g)

Next == Owner \/ \E g \in G : Worker(g)
Spec == Init /\ [][Next]_vars /\ WF_vars(Owner) /\ \A g \in G : WF_vars(Worker(g))

(* Safety. *)
\* Each short message's credit comes back once at most, and a room's count
\* is the held Room's unspent credits and its messages' credits still out.
BackOnce == \A m \in M : back[m] <= 1
Counted == \A r \in R : refs[r] = (IF held = r THEN Credits - commits ELSE 0) + Cardinality({m \in M : msg[m].r = r /\ Out(m)})
\* A group's members are read from their rooms' hand-outs: no room was
\* handed out again over their bytes.
ReadsItsBytes == \A g \in G : wst[g] = "queued" => \A m \in InGroup(g) : Short(m) => gen[msg[m].r] = msg[m].gen
\* A group is filled again only once its last epoch has completed.
ReusedAfterEpoch == openG # 0 => wst[openG] = "idle"
\* An event reads its output (a batch's digests) only once its group wrote it.
ReadAfterWritten == \A m \in M : msg[m].pc = "taken" /\ msg[m].g # 0 => out[m]
\* With the Pipeline and its Room dropped, every credit is back.
AllBack == dropped /\ held = 0 => \A r \in R : refs[r] = 0

(* Liveness: an ended message's event is taken, unless the Pipeline is
   dropped first. *)
EventsTaken == \A m \in M : (msg[m].pc \in {"wait", "aborted"}) ~> (msg[m].pc = "taken" \/ dropped)
=============================================================================
