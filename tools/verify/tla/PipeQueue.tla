------------------------------- MODULE PipeQueue -------------------------------
(* threads/src/lanes.rs's Source, a Pipeline's action queue, and the rings
   of threads/src/pipeline.rs that hold what it hands out (Ring: push_back
   asserts its capacity in every build).

   The queue: the owner publishes actions (publish_actions), action p at
   slot p % ActionRing, under the assert that every action not yet taken
   fits (published - claimed + n <= ActionRing), then one Release store of
   `published`; it wakes a parked worker where two or more wait, leaving a
   lone one to the owner. A taker, a worker (run_one, serve) or the owner
   itself (run_waiting_action), reads the slot at `claimed`, then claims it
   by compare-and-swap (take); a worker that takes one with two or more
   still waiting wakes the next (serve). A worker that finds none sets its
   parked bit, looks again, and parks (Park.tla's handshake, its two steps
   here); a wake (wake_one) clears a bit and sends that worker looking.

   What the owner hands out, and the ring each comes back to:
     a slot's tasks   1 to MaxPieces actions on a slot from free_slots
                      (SlotRing), back once they all ran (reap)
     a room piece     1 action on a node from free_pieces (PieceRing), back
                      once it ran (drain_pieces); a whole Room's piece also
                      takes a room from local_free_rooms (RoomRing, filled
                      by a scan of the free rooms when empty, try_take_room),
                      free again once the piece ran
     a group          1 action on a group that ran (acquire_free_group)
   The rings' capacities are the code's: m, p_cap = rooms + m + 1,
   rooms.max(1), and actions_cap = m * MAX_SLOT_PIECES + p_cap + g_cap.
   Here the three are independent; in the code a slot is used one way and a
   short Room's piece shares its Room, so the code's queue holds fewer:
   the bound holds for this looser use, and this use meets it.

   The owner's waits. Spinning for a node or a group (alloc_piece_node,
   acquire_free_group), it runs waiting actions. Waiting for its work
   (ready, message, room), in block_on it first runs every waiting action;
   in any executor it then calls wake_for_waiting and sleeps until an
   action has run (the WakerSlot's notify, which Waker.tla checks).
   g_cap here is `Groups`, against m.clamp(4, 256) in the code. *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Workers, Slots, MaxPieces, Rooms, Groups, Dispatches

W == 1..Workers
OWNER == 0
Takers == W \cup {OWNER}
Nodes == Rooms + Slots + 1
SlotRing == Slots
PieceRing == Nodes
RoomRing == IF Rooms > 1 THEN Rooms ELSE 1
ActionRing == Slots * MaxPieces + Nodes + Groups
A == 1..Dispatches * MaxPieces        \* publication numbers (the code's from 0; here p is its p - 1)

VARIABLES published, claimed, ring, what, ran,   \* the queue; each slot's publication; each action's owner; its runs
          take, running,                          \* each taker's read (number, slot's publication) and the action it runs
          wpc,                                    \* each worker: look, cas, run, bit, parked
          freeSlots, slotLeft,                    \* free_slots; each slot's actions not yet run
          freePieces, node,                       \* free_pieces; each node: free, out, ran
          localRooms, room,                       \* local_free_rooms; each room: free, listed, busy
          group,                                  \* each group: free, out
          blockOn, opc, spinFor,                  \* the executor; the owner's place; what it spins for
          made, runs, slept, fault                \* dispatches; actions run; runs a wait began after; an assert failed

vars == <<published, claimed, ring, what, ran, take, running, wpc, freeSlots, slotLeft, freePieces, node,
          localRooms, room, group, blockOn, opc, spinFor, made, runs, slept, fault>>
queue == <<published, claimed, ring, what, ran, take, running, wpc>>
held == <<freeSlots, slotLeft, freePieces, node, localRooms, room, group>>
NONE == [n |-> 0, gen |-> 0]

Init == /\ published = 0 /\ claimed = 0 /\ ring = [i \in 0..ActionRing - 1 |-> 0]
        /\ what = [a \in A |-> <<"none", 0, 0>>] /\ ran = [a \in A |-> 0]
        /\ take = [t \in Takers |-> NONE] /\ running = [t \in Takers |-> NONE]
        /\ wpc = [w \in W |-> "look"]
        /\ freeSlots = [i \in 1..Slots |-> i] /\ slotLeft = [s \in 1..Slots |-> 0]
        /\ freePieces = [i \in 1..Nodes |-> i] /\ node = [n \in 1..Nodes |-> "free"]
        /\ localRooms = <<>> /\ room = [r \in 1..Rooms |-> "free"]
        /\ group = [g \in 1..Groups |-> "free"]
        /\ blockOn \in BOOLEAN /\ opc = "idle" /\ spinFor = "none" /\ made = 0 /\ runs = 0 /\ slept = 0 /\ fault = "none"

Waiting == published - claimed
Parked == {w \in W : wpc[w] \in {"bit", "parked"}}

(* wake_one, for worker w's next place: one parked worker goes looking. *)
WakeOne(w, next) ==
    IF Parked = {} THEN wpc' = [wpc EXCEPT ![w] = next]
    ELSE \E v \in Parked : wpc' = [wpc EXCEPT ![w] = next, ![v] = "look"]
Wake == IF Parked = {} THEN UNCHANGED wpc ELSE \E v \in Parked : wpc' = [wpc EXCEPT ![v] = "look"]

(* publish_actions: n actions for `owner`, or its assert. *)
Publish(n, owner) ==
    IF published - claimed + n > ActionRing
    THEN fault' = "action ring" /\ UNCHANGED <<published, ring, what, wpc>>
    ELSE /\ ring' = [i \in 0..ActionRing - 1 |->
                       IF \E p \in published + 1..published + n : p % ActionRing = i
                       THEN CHOOSE p \in published + 1..published + n : p % ActionRing = i ELSE ring[i]]
         /\ what' = [a \in A |-> IF a > published /\ a <= published + n THEN owner ELSE what[a]]
         /\ published' = published + n
         /\ IF published + n - claimed >= 2 THEN Wake ELSE UNCHANGED wpc
         /\ UNCHANGED fault
\* Ring.push_back, with its assert.
PushRing(q, cap, x, name) == IF Len(q) < cap THEN q' = Append(q, x) /\ UNCHANGED fault ELSE fault' = name /\ UNCHANGED q

(* take: read the slot at `claimed`; then compare-and-swap. *)
Read(t) == /\ claimed < published
           /\ take' = [take EXCEPT ![t] = [n |-> claimed + 1, gen |-> ring[(claimed + 1) % ActionRing]]]
Won(t) == claimed + 1 = take[t].n
Cas(t) == /\ IF Won(t)
              THEN claimed' = claimed + 1 /\ running' = [running EXCEPT ![t] = take[t]] /\ ran' = [ran EXCEPT ![take[t].n] = @ + 1]
              ELSE UNCHANGED <<claimed, running, ran>>
          /\ take' = [take EXCEPT ![t] = NONE]

(* An action's run: its slot's, node's, room's or group's part is done. *)
Done(t) == LET o == what[running[t].n] IN
    /\ slotLeft' = IF o[1] = "slot" THEN [slotLeft EXCEPT ![o[2]] = @ - 1] ELSE slotLeft
    /\ node' = IF o[1] = "piece" THEN [node EXCEPT ![o[2]] = "ran"] ELSE node
    /\ room' = IF o[1] = "piece" /\ o[3] # 0 THEN [room EXCEPT ![o[3]] = "free"] ELSE room
    /\ group' = IF o[1] = "group" THEN [group EXCEPT ![o[2]] = "free"] ELSE group
    /\ running' = [running EXCEPT ![t] = NONE] /\ runs' = runs + 1
    /\ UNCHANGED <<freeSlots, freePieces, localRooms>>

(* The workers. *)
Look(w) == /\ wpc[w] = "look"
           /\ IF claimed < published THEN Read(w) /\ wpc' = [wpc EXCEPT ![w] = "cas"]
              ELSE wpc' = [wpc EXCEPT ![w] = "bit"] /\ UNCHANGED take
           /\ UNCHANGED <<published, claimed, ring, what, ran, running, held, blockOn, spinFor, opc, made, runs, slept, fault>>
Claim(w) == /\ wpc[w] = "cas"
            /\ Cas(w)
            /\ IF ~Won(w) THEN wpc' = [wpc EXCEPT ![w] = "look"]
               ELSE IF published - (claimed + 1) >= 2 THEN WakeOne(w, "run")   \* serve's chain
               ELSE wpc' = [wpc EXCEPT ![w] = "run"]
            /\ UNCHANGED <<published, ring, what, held, blockOn, spinFor, opc, made, runs, slept, fault>>
Run(w) == /\ wpc[w] = "run"
          /\ Done(w) /\ wpc' = [wpc EXCEPT ![w] = "look"]
          /\ UNCHANGED <<published, claimed, ring, what, ran, take, blockOn, spinFor, opc, made, slept, fault>>
\* With its bit set, it looks again: work visible, or it parks.
Recheck(w) == /\ wpc[w] = "bit"
              /\ wpc' = [wpc EXCEPT ![w] = IF claimed < published THEN "look" ELSE "parked"]
              /\ UNCHANGED <<published, claimed, ring, what, ran, take, running, held, blockOn, spinFor, opc, made, runs, slept, fault>>
Worker(w) == Look(w) \/ Claim(w) \/ Run(w) \/ Recheck(w)

(* The owner. *)
Idle == opc = "idle" /\ fault = "none"
Hand == Idle /\ made < Dispatches
\* A slot's tasks.
Tasks == /\ Hand /\ freeSlots # <<>>
         /\ \E n \in 1..MaxPieces : Publish(n, <<"slot", Head(freeSlots), 0>>) /\ slotLeft' = [slotLeft EXCEPT ![Head(freeSlots)] = n]
         /\ freeSlots' = Tail(freeSlots) /\ made' = made + 1
         /\ UNCHANGED <<claimed, ran, take, running, freePieces, node, localRooms, room, group, blockOn, spinFor, opc, runs, slept>>
\* A room piece: a node, and for a whole Room a room off the local ring.
Piece(r) == /\ Hand /\ freePieces # <<>>
            /\ Publish(1, <<"piece", Head(freePieces), r>>)
            /\ node' = [node EXCEPT ![Head(freePieces)] = "out"] /\ freePieces' = Tail(freePieces) /\ made' = made + 1
            /\ UNCHANGED <<claimed, ran, take, running, freeSlots, slotLeft, group, blockOn, spinFor, opc, runs, slept>>
ShortPiece == Piece(0) /\ UNCHANGED <<localRooms, room>>
WholePiece == /\ localRooms # <<>> /\ Piece(Head(localRooms))
              /\ room' = [room EXCEPT ![Head(localRooms)] = "busy"] /\ localRooms' = Tail(localRooms)
\* try_take_room's scan of the rooms, with the local ring empty.
RECURSIVE ListFrom(_, _)
ListFrom(q, r) == IF r > Rooms THEN q ELSE ListFrom(IF room[r] = "free" THEN Append(q, r) ELSE q, r + 1)
Scan == /\ Idle /\ localRooms = <<>> /\ \E r \in 1..Rooms : room[r] = "free"
        /\ LET list == ListFrom(<<>>, 1) IN
           IF Len(list) <= RoomRing
           THEN localRooms' = list /\ room' = [r \in 1..Rooms |-> IF room[r] = "free" THEN "listed" ELSE room[r]] /\ UNCHANGED fault
           ELSE fault' = "room ring" /\ UNCHANGED <<localRooms, room>>
        /\ UNCHANGED <<queue, freeSlots, slotLeft, freePieces, node, group, blockOn, spinFor, opc, made, runs, slept>>
\* A group that ran.
Group == /\ Hand /\ \E g \in 1..Groups : group[g] = "free"
         /\ LET g == CHOOSE g \in 1..Groups : group[g] = "free" IN
            Publish(1, <<"group", g, 0>>) /\ group' = [group EXCEPT ![g] = "out"]
         /\ made' = made + 1
         /\ UNCHANGED <<claimed, ran, take, running, freeSlots, slotLeft, freePieces, node, localRooms, room, blockOn, spinFor, opc, runs, slept>>
\* Back on their rings: a slot whose tasks all ran, a node whose piece ran.
InRing(q, x) == \E i \in 1..Len(q) : q[i] = x
Reap(s) == /\ Idle /\ slotLeft[s] = 0 /\ ~InRing(freeSlots, s)
           /\ PushRing(freeSlots, SlotRing, s, "slot ring")
           /\ UNCHANGED <<queue, slotLeft, freePieces, node, localRooms, room, group, blockOn, spinFor, opc, made, runs, slept>>
Drain(n) == /\ Idle /\ node[n] = "ran"
            /\ PushRing(freePieces, PieceRing, n, "piece ring") /\ node' = [node EXCEPT ![n] = "free"]
            /\ UNCHANGED <<queue, freeSlots, slotLeft, localRooms, room, group, blockOn, spinFor, opc, made, runs, slept>>

\* run_waiting_action, in a spin or a block_on wait: read, claim, run.
Runs == (opc = "spin") \/ (opc = "wait" /\ blockOn)
ORead == /\ Runs /\ claimed < published /\ Read(OWNER)
         /\ opc' = IF opc = "spin" THEN "spincas" ELSE "waitcas"
         /\ UNCHANGED <<published, claimed, ring, what, ran, running, wpc, held, blockOn, spinFor, made, runs, slept, fault>>
OClaim == /\ opc \in {"spincas", "waitcas"}
          /\ Cas(OWNER)
          /\ opc' = CASE Won(OWNER) /\ opc = "spincas" -> "spinrun" [] Won(OWNER) -> "waitrun"
                      [] opc = "spincas" -> "spin" [] OTHER -> "wait"
          /\ UNCHANGED <<published, ring, what, wpc, held, blockOn, spinFor, made, runs, slept, fault>>
ORun == /\ opc \in {"spinrun", "waitrun"}
        /\ Done(OWNER) /\ opc' = IF opc = "spinrun" THEN "idle" ELSE "wait"
        /\ UNCHANGED <<published, claimed, ring, what, ran, take, wpc, blockOn, spinFor, made, slept, fault>>
\* Spinning for a node (none free, none to drain) or a group (none ran);
\* the spin ends once one is.
NodeBack == \E n \in 1..Nodes : node[n] = "ran"
GroupBack == \E g \in 1..Groups : group[g] = "free"
Spin == /\ Hand
        /\ \/ freePieces = <<>> /\ ~NodeBack /\ spinFor' = "node"
           \/ ~GroupBack /\ spinFor' = "group"
        /\ opc' = "spin" /\ UNCHANGED <<queue, held, blockOn, made, runs, slept, fault>>
SpinEnd == /\ opc = "spin" /\ IF spinFor = "node" THEN NodeBack ELSE GroupBack
           /\ opc' = "idle" /\ spinFor' = "none" /\ UNCHANGED <<queue, held, blockOn, made, runs, slept, fault>>
\* A wait for its work: run what waits (block_on), then wake_for_waiting
\* and sleep until an action has run since.
Outstanding == \E a \in A : a <= published /\ ran[a] = 0
Busy == Outstanding \/ \E t \in Takers : running[t] # NONE
\* (`slept`: the runs the wait began after; the owner has reaped those.)
StartWait == /\ Idle /\ Busy
             /\ opc' = "wait" /\ slept' = runs /\ UNCHANGED <<queue, held, blockOn, spinFor, made, runs, fault>>
\* Registered, it looks again: a run since, and it returns.
Sleep == /\ opc = "wait" /\ (~blockOn \/ claimed = published)
         /\ IF Waiting > 0 THEN Wake ELSE UNCHANGED wpc        \* wake_for_waiting
         /\ opc' = IF runs > slept THEN "idle" ELSE "sleep"
         /\ UNCHANGED <<published, claimed, ring, what, ran, take, running, held, blockOn, spinFor, made, runs, slept, fault>>
Woken == /\ opc = "sleep" /\ runs > slept
         /\ opc' = "idle" /\ UNCHANGED <<queue, held, blockOn, spinFor, made, runs, slept, fault>>
Finish == /\ Idle /\ made = Dispatches /\ ~Busy
          /\ opc' = "done" /\ UNCHANGED <<queue, held, blockOn, spinFor, made, runs, slept, fault>>

Owner == Tasks \/ ShortPiece \/ WholePiece \/ Scan \/ Group \/ (\E s \in 1..Slots : Reap(s)) \/ (\E n \in 1..Nodes : Drain(n))
         \/ ORead \/ OClaim \/ ORun \/ Spin \/ SpinEnd \/ StartWait \/ Sleep \/ Woken \/ Finish
Next == Owner \/ \E w \in W : Worker(w)
Spec == Init /\ [][Next]_vars /\ WF_vars(Owner) /\ \A w \in W : WF_vars(Worker(w))

(* Safety. *)
\* No ring is pushed past its capacity (each assert holds).
RingsHold == fault = "none"
\* An action is run once, and is the one published at its number: its slot
\* was not written again before it was taken.
RunOnce == \A a \in A : ran[a] <= 1
ReadsItsAction == \A t \in Takers : running[t] # NONE => running[t].gen = running[t].n
\* Each item is on its ring at most once.
OnceEach == /\ \A i, j \in 1..Len(freeSlots) : i # j => freeSlots[i] # freeSlots[j]
            /\ \A i, j \in 1..Len(freePieces) : i # j => freePieces[i] # freePieces[j]
            /\ \A i, j \in 1..Len(localRooms) : i # j => localRooms[i] # localRooms[j]

\* The owner never sleeps on actions waiting with every worker parked: in
\* block_on it ran them, and otherwise wake_for_waiting woke one (and a
\* worker parks only when none waits).
NoSleepOnWaiting == opc = "sleep" /\ Waiting > 0 => \E w \in W : wpc[w] # "parked"

(* Liveness: every action handed out is run, by a worker or the owner, and
   the owner finishes: no wait sleeps on work no one takes. *)
Finishes == <>(opc = "done" \/ fault # "none")
=============================================================================
