------------------------------ MODULE PipeStorage ------------------------------
(* threads/src/pipeline.rs: a storage outliving its Pipeline. A storage
   (rooms and the rest) is never freed: the last of its holders puts it on
   the free list for the next Pipeline (PipeStorage::release_n). Its
   Pipeline holds it while alive; a Room may outlive the Pipeline on another
   thread. Pipeline::drop, with no work in flight, first reserves a hold for
   every room, then stamps each room's count with the closing bit: a room
   whose count was 0 is cleared again and its hold given back with the
   Pipeline's own; a room still counted is a surviving Room's, whose drop
   (Room::drop) sees the bit, clears the count and gives its hold back.

   Each action is one atomic operation. `Survivors` of the `Rooms` rooms are
   held by Rooms alive on another thread, with credits left on their counts;
   the next Pipeline takes the storage off the free list and hands out the
   rooms whose counts are 0. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Rooms, Survivors

R == 1..Rooms
S == 1..Survivors

VARIABLES holders, pushes, takes,     \* the holds; pushes onto and takes off the free list
          refs, closing,              \* each room's count and closing bit
          live,                       \* the surviving Rooms not yet dropped
          dpc, i, survivors,          \* Pipeline::drop's place, the room it stamps, survivors seen
          rpc,                        \* each surviving Room's drop
          nextRooms                   \* the rooms the next Pipeline has handed out

vars == <<holders, pushes, takes, refs, closing, live, dpc, i, survivors, rpc, nextRooms>>

Init == /\ holders = 1 /\ pushes = 0 /\ takes = 0
        /\ refs = [r \in R |-> IF r \in S THEN 2 ELSE 0] /\ closing = [r \in R |-> FALSE]
        /\ live = S /\ dpc = "reserve" /\ i = 1 /\ survivors = 0
        /\ rpc = [r \in S |-> "drop"] /\ nextRooms = {}

\* release_n: the last of the holds puts the storage on the free list.
ReleaseN(n) == /\ holders' = holders - n
               /\ pushes' = IF holders = n THEN pushes + 1 ELSE pushes

(* Pipeline::drop *)
Reserve ==   /\ dpc = "reserve"
             /\ holders' = holders + Rooms /\ dpc' = "stamp"
             /\ UNCHANGED <<pushes, takes, refs, closing, live, i, survivors, rpc, nextRooms>>
Stamp ==     /\ dpc = "stamp" /\ i <= Rooms
             /\ closing' = [closing EXCEPT ![i] = TRUE]              \* fetch_or
             /\ IF refs[i] # 0 THEN survivors' = survivors + 1 /\ i' = i + 1 /\ UNCHANGED dpc
                ELSE dpc' = "unstamp" /\ UNCHANGED <<i, survivors>>
             /\ UNCHANGED <<holders, pushes, takes, refs, live, rpc, nextRooms>>
Unstamp ==   /\ dpc = "unstamp"
             /\ closing' = [closing EXCEPT ![i] = FALSE] /\ i' = i + 1 /\ dpc' = "stamp"
             /\ UNCHANGED <<holders, pushes, takes, refs, live, survivors, rpc, nextRooms>>
Release ==   /\ dpc = "stamp" /\ i > Rooms
             /\ ReleaseN((Rooms - survivors) + 1) /\ dpc' = "dropped"
             /\ UNCHANGED <<takes, refs, closing, live, i, survivors, rpc, nextRooms>>

(* A surviving Room's drop, on another thread. *)
RoomDrop(r) == /\ rpc[r] = "drop"
               /\ refs' = [refs EXCEPT ![r] = 0] /\ live' = live \ {r}       \* fetch_sub of its credits
               /\ rpc' = [rpc EXCEPT ![r] = IF closing[r] THEN "clear" ELSE "end"]
               /\ UNCHANGED <<holders, pushes, takes, closing, dpc, i, survivors, nextRooms>>
RoomClear(r) == /\ rpc[r] = "clear"
                /\ closing' = [closing EXCEPT ![r] = FALSE] /\ rpc' = [rpc EXCEPT ![r] = "release"]
                /\ UNCHANGED <<holders, pushes, takes, refs, live, dpc, i, survivors, nextRooms>>
RoomRelease(r) == /\ rpc[r] = "release"
                  /\ ReleaseN(1) /\ rpc' = [rpc EXCEPT ![r] = "end"]
                  /\ UNCHANGED <<takes, refs, closing, live, dpc, i, survivors, nextRooms>>

(* The next Pipeline: takes the storage off the free list, hands out the
   rooms whose counts are 0. *)
Take ==      /\ pushes > takes
             /\ takes' = takes + 1 /\ holders' = holders + 1
             /\ UNCHANGED <<pushes, refs, closing, live, dpc, i, survivors, rpc, nextRooms>>
HandOut(r) == /\ takes > 0 /\ refs[r] = 0 /\ ~closing[r] /\ r \notin nextRooms
              /\ refs' = [refs EXCEPT ![r] = 3] /\ nextRooms' = nextRooms \cup {r}
              /\ UNCHANGED <<holders, pushes, takes, closing, live, dpc, i, survivors, rpc>>

Drop == Reserve \/ Stamp \/ Unstamp \/ Release
Next == Drop \/ Take \/ (\E r \in R : HandOut(r)) \/ \E r \in S : RoomDrop(r) \/ RoomClear(r) \/ RoomRelease(r)
Spec == Init /\ [][Next]_vars /\ WF_vars(Drop) /\ WF_vars(Take)
        /\ \A r \in S : WF_vars(RoomDrop(r) \/ RoomClear(r) \/ RoomRelease(r))

(* On the free list only once no Pipeline or Room holds it, and once. *)
FreeOnlyUnheld == /\ pushes > takes => live = {} /\ dpc = "dropped"
                  /\ pushes <= 1
(* The next Pipeline never hands out a room a surviving Room still holds. *)
NoSharedRoom == nextRooms \cap live = {}
HoldsNonNegative == holders >= 0
(* The storage goes back on the free list. *)
Returns == <>(pushes = 1)
=============================================================================
