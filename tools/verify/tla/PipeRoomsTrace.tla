---------------------------- MODULE PipeRoomsTrace ----------------------------
(* Trace validation of PipeRooms.tla against threads/src/pipeline.rs: every
   schedule Shuttle runs of tests/shuttle_pipeline.rs's
   a_wait_for_a_room_ends_when_another_thread_drops_one (one Room: a whole
   Room committed, the Room dropped on another thread while the owner waits
   for one, the rest committed from the Room it gets, then the event) is
   logged, an atomic operation a step, and check.py turns each log into the
   PipeRooms.tla actions it is (`Traces`). One the model does not allow
   leaves no step, a deadlock TLC reports with the trace. A trace taken
   whole ends with the owner's events all taken (Ends). *)
EXTENDS PipeRooms, Sequences

CONSTANT Traces

VARIABLES t, i
tvars == <<vars, t, i>>

TInit == Init /\ t \in 1..Len(Traces) /\ i = 0

\* After a commit: the owner keeps the Room, drops it, or hands it on.
AfterTo(k) == After /\ CASE k = "keep" -> opc' = "room" /\ held' = held
                         [] k = "drop" -> opc' = "drop"
                         [] k = "other" -> opc' = "room" /\ held' = 0

Do(e) == CASE e.a = "TakeRoom" -> TakeRoom
           [] e.a = "RoomCheck" -> RoomCheck
           [] e.a = "RoomWait" -> RoomWait
           [] e.a = "Commit" -> Commit
           [] e.a = "After" -> AfterTo(e.k)
           [] e.a = "OwnerDrop" -> OwnerDrop
           [] e.a = "EndCommits" -> EndCommits
           [] e.a = "Events" -> Events
           [] e.a = "EventCheck" -> EventCheck
           [] e.a = "EventWait" -> EventWait
           [] e.a = "Repoll" -> Repoll
           [] e.a = "Clear" -> Clear
           [] e.a = "OtherDrop" -> OtherDrop(e.r)
           [] e.a = "Read" -> Read(e.p)
           [] e.a = "Hash" -> Hash(e.p)
           [] e.a = "Release" -> Release(e.p)
           [] e.a = "Publish" -> Publish(e.p)

TNext == \/ /\ i < Len(Traces[t]) /\ Do(Traces[t][i + 1]) /\ i' = i + 1 /\ UNCHANGED t
         \/ /\ i = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == i = Len(Traces[t]) => opc = "finished"
=============================================================================
