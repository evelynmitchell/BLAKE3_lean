------------------------------- MODULE PipeRooms -------------------------------
(* threads/src/pipeline.rs: Rooms, their credits, and the pieces hashed out
   of them. A Room is handed out with all `Credits` credits on its count
   (refs, init_taken); each commit spends one of the Room's, which the piece
   carries to the worker (take_credit, commit); the worker reads the piece's
   bytes, writes its output, gives the credit back, then marks the piece
   done and wakes the owner (run_room_piece, finished). A Room's drop gives
   back the credits it has left, and wakes the owner when that frees the
   room (Room::drop). A room is free, and may be handed out over the same
   bytes, when its count is 0 (try_take_room). A Room is Send: one may be
   dropped on another thread ("other") while the owner waits for a room.

   The owner makes `Commits` commits, each from a free room or the Room it
   holds, then waits for every piece's event. Waits use the WakerSlot's
   contract, which Waker.tla checks: register, re-check, and a notify after
   it wakes the waiter. `gen` counts each room's hand-outs: a piece reads
   its room's bytes of the hand-out it was committed from. *)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Rooms, Credits, Commits

R == 1..Rooms
P == 1..Commits

VARIABLES refs, gen, holder, commits,  \* each room's count and hand-outs; who holds a Room, its commits
          piece,                        \* each piece: its room, its hand-out, its place
          made,                         \* commits made
          registered, woken,            \* the owner's WakerSlot
          opc, held                     \* the owner's place, and the room it holds (0: none)

vars == <<refs, gen, holder, commits, piece, made, registered, woken, opc, held>>

Init == /\ refs = [r \in R |-> 0] /\ gen = [r \in R |-> 0]
        /\ holder = [r \in R |-> "none"] /\ commits = [r \in R |-> 0]
        /\ piece = [p \in P |-> [room |-> 0, gen |-> 0, pc |-> "none", out |-> FALSE, done |-> FALSE]]
        /\ made = 0 /\ registered = FALSE /\ woken = FALSE /\ opc = "room" /\ held = 0

Free(r) == refs[r] = 0 /\ holder[r] = "none"
Notify == IF registered THEN registered' = FALSE /\ woken' = TRUE ELSE UNCHANGED <<registered, woken>>

(* The owner *)
\* room(): take a free room (try_take_room), else wait: register, re-check.
TakeRoom ==   /\ opc = "room" /\ made < Commits
              /\ IF held # 0 THEN opc' = "commit" /\ UNCHANGED <<refs, gen, holder, commits, held, registered>>
                 ELSE IF \E r \in R : Free(r)
                 THEN \E r \in R : /\ Free(r)
                                   /\ refs' = [refs EXCEPT ![r] = Credits] /\ gen' = [gen EXCEPT ![r] = gen[r] + 1]
                                   /\ holder' = [holder EXCEPT ![r] = "owner"] /\ commits' = [commits EXCEPT ![r] = 0]
                                   /\ held' = r /\ opc' = "commit" /\ UNCHANGED registered
                 ELSE registered' = TRUE /\ opc' = "roomcheck" /\ UNCHANGED <<refs, gen, holder, commits, held>>
              /\ UNCHANGED <<piece, made, woken>>
RoomCheck ==  /\ opc = "roomcheck"
              /\ IF \E r \in R : Free(r) THEN registered' = FALSE /\ opc' = "room" ELSE opc' = "roomwait" /\ UNCHANGED registered
              /\ UNCHANGED <<refs, gen, holder, commits, piece, made, woken, held>>
RoomWait ==   /\ opc = "roomwait" /\ woken
              /\ woken' = FALSE /\ opc' = "room"
              /\ UNCHANGED <<refs, gen, holder, commits, piece, made, registered, held>>
\* commit: spend one of the Room's credits on the next piece. A Room never
\* gives out its last: at Credits - 1 commits it takes a new set.
Commit ==     /\ opc = "commit"
              /\ LET r == held
                     renew == commits[r] = Credits - 1
                 IN /\ refs' = IF renew THEN [refs EXCEPT ![r] = refs[r] + (Credits - 1)] ELSE refs
                    /\ commits' = [commits EXCEPT ![r] = (IF renew THEN 0 ELSE commits[r]) + 1]
                    /\ piece' = [piece EXCEPT ![made + 1] = [room |-> r, gen |-> gen[r], pc |-> "queued", out |-> FALSE, done |-> FALSE]]
              /\ made' = made + 1 /\ opc' = "after"
              /\ UNCHANGED <<gen, holder, registered, woken, held>>
\* After a commit: keep the Room, drop it, or hand it to another thread.
After ==      /\ opc = "after"
              /\ \/ opc' = "room" /\ UNCHANGED <<refs, holder, held, registered, woken>>
                 \/ opc' = "drop" /\ UNCHANGED <<refs, holder, held, registered, woken>>
                 \/ /\ holder' = [holder EXCEPT ![held] = "other"] /\ held' = 0 /\ opc' = "room"
                    /\ UNCHANGED <<refs, registered, woken>>
              /\ UNCHANGED <<gen, commits, piece, made>>
DropRoom(r) == \* Room::drop: give back the credits left; free: wake the owner.
              LET unused == Credits - commits[r]
                  prev == refs[r]
              IN /\ refs' = [refs EXCEPT ![r] = refs[r] - unused]
                 /\ holder' = [holder EXCEPT ![r] = "none"]
                 /\ IF prev = unused THEN Notify ELSE UNCHANGED <<registered, woken>>
OwnerDrop ==  /\ opc = "drop"
              /\ DropRoom(held) /\ held' = 0 /\ opc' = "room"
              /\ UNCHANGED <<gen, commits, piece, made>>
\* Every commit made: drop the Room held, then wait for every piece's event.
EndCommits == /\ opc = "room" /\ made = Commits
              /\ IF held # 0 THEN DropRoom(held) ELSE UNCHANGED <<refs, holder, registered, woken>>
              /\ held' = 0 /\ opc' = "events"
              /\ UNCHANGED <<gen, commits, piece, made>>
Events ==     /\ opc = "events"
              /\ IF \A p \in P : piece[p].done THEN opc' = "finished" /\ UNCHANGED registered
                 ELSE registered' = TRUE /\ opc' = "eventcheck"
              /\ UNCHANGED <<refs, gen, holder, commits, piece, made, woken, held>>
EventCheck == /\ opc = "eventcheck"
              /\ IF \A p \in P : piece[p].done THEN registered' = FALSE /\ opc' = "finished"
                 ELSE opc' = "eventwait" /\ UNCHANGED registered
              /\ UNCHANGED <<refs, gen, holder, commits, piece, made, woken, held>>
EventWait ==  /\ opc = "eventwait" /\ woken
              /\ woken' = FALSE /\ opc' = "events"
              /\ UNCHANGED <<refs, gen, holder, commits, piece, made, registered, held>>

(* Another thread, holding a Room it was handed: it drops it. *)
OtherDrop(r) == /\ holder[r] = "other"
                /\ DropRoom(r)
                /\ UNCHANGED <<gen, commits, piece, made, opc, held>>

(* A worker running piece p: read the bytes, write the output, give the
   credit back, publish done and wake (run_room_piece, finished). *)
Read(p) ==    /\ piece[p].pc = "queued"
              /\ piece' = [piece EXCEPT ![p].pc = "reading"]
              /\ UNCHANGED <<refs, gen, holder, commits, made, registered, woken, opc, held>>
Hash(p) ==    /\ piece[p].pc = "reading"
              /\ piece' = [piece EXCEPT ![p].pc = "release", ![p].out = TRUE]
              /\ UNCHANGED <<refs, gen, holder, commits, made, registered, woken, opc, held>>
Release(p) == /\ piece[p].pc = "release"
              /\ refs' = [refs EXCEPT ![piece[p].room] = refs[piece[p].room] - 1]
              /\ piece' = [piece EXCEPT ![p].pc = "publish"]
              /\ UNCHANGED <<gen, holder, commits, made, registered, woken, opc, held>>
Publish(p) == /\ piece[p].pc = "publish"
              /\ piece' = [piece EXCEPT ![p].pc = "end", ![p].done = TRUE]
              /\ Notify
              /\ UNCHANGED <<refs, gen, holder, commits, made, opc, held>>

Owner == TakeRoom \/ RoomCheck \/ RoomWait \/ Commit \/ After \/ OwnerDrop \/ EndCommits \/ Events \/ EventCheck \/ EventWait
Worker(p) == Read(p) \/ Hash(p) \/ Release(p) \/ Publish(p)
Next == Owner \/ (\E r \in R : OtherDrop(r)) \/ \E p \in P : Worker(p)
Spec == Init /\ [][Next]_vars /\ WF_vars(Owner) /\ \A r \in R : WF_vars(OtherDrop(r)) /\ \A p \in P : WF_vars(Worker(p))

(* A piece reads its room's bytes of the hand-out it was committed from: the
   room was not handed out again over them meanwhile. *)
ReadsItsBytes == \A p \in P : piece[p].pc = "reading" => gen[piece[p].room] = piece[p].gen
(* A piece is published done only with its output written. *)
DoneAfterHash == \A p \in P : piece[p].done => piece[p].out
(* A room's count never goes below zero. *)
CountsNonNegative == \A r \in R : refs[r] >= 0
(* No wake is lost: the owner makes every commit and sees every event. *)
Finishes == <>(opc = "finished")
=============================================================================
