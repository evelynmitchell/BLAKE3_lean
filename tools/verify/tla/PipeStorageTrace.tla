--------------------------- MODULE PipeStorageTrace ---------------------------
(* Trace validation of PipeStorage.tla against threads/src/pipeline.rs:
   every schedule Shuttle runs of tests/shuttle_pipeline.rs's
   a_storage_outlives_its_pipeline_in_its_rooms (a Pipeline of three Rooms
   dropped while two of its Rooms are alive on threads of their own, then
   the next Pipeline of its size, which takes the storage if it is free by
   then, and a room) is logged, an atomic operation a step, and check.py
   turns each log into the PipeStorage.tla actions it is (`Traces`). One the
   model does not allow leaves no step, a deadlock TLC reports with the
   trace. A trace taken whole ends with the storage given back and every
   surviving Room dropped (Ends). *)
EXTENDS PipeStorage, Sequences

CONSTANT Traces

VARIABLES t, j
tvars == <<vars, t, j>>

TInit == Init /\ t \in 1..Len(Traces) /\ j = 0

Do(e) == CASE e.a = "Reserve" -> Reserve
           [] e.a = "Stamp" -> Stamp
           [] e.a = "Unstamp" -> Unstamp
           [] e.a = "Release" -> Release
           [] e.a = "RoomDrop" -> RoomDrop(e.r)
           [] e.a = "RoomClear" -> RoomClear(e.r)
           [] e.a = "RoomRelease" -> RoomRelease(e.r)
           [] e.a = "Take" -> Take
           [] e.a = "HandOut" -> HandOut(e.r)

TNext == \/ /\ j < Len(Traces[t]) /\ Do(Traces[t][j + 1]) /\ j' = j + 1 /\ UNCHANGED t
         \/ /\ j = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == j = Len(Traces[t]) => pushes = 1 /\ dpc = "dropped" /\ live = {}
=============================================================================
