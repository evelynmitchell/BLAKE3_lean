---------------------------- MODULE PipeShortTrace ----------------------------
(* Trace validation of PipeShort.tla against threads/src/pipeline.rs: every
   schedule Shuttle runs of tests/shuttle_pipeline.rs's
   short_messages_share_a_room_and_a_group (three short messages from one
   Room, the first and last ended into one group, the second aborted while
   open; the Room dropped, the events taken, the Pipeline dropped) is
   logged: the scenario's own calls, the groups the Pipeline publishes, and
   the atomic operations of the Room's count and the groups' epochs.
   check.py turns each log into the PipeShort.tla actions it is (`Traces`).
   One the model does not allow leaves no step, a deadlock TLC reports with
   the trace. A trace taken whole ends with every event taken and the
   Pipeline dropped (Ends). *)
EXTENDS PipeShort

CONSTANT Traces

VARIABLES t, j
tvars == <<vars, t, j>>

TInit == Init /\ t \in 1..Len(Traces) /\ j = 0

Do(e) == CASE e.a = "TakeRoom" -> TakeRoom
           [] e.a = "Commit" -> Commit
           [] e.a = "OnMsg" -> OnMsgE(e.m, e.early)
           [] e.a = "AbortShort" -> AbortShort(e.m)
           [] e.a = "DropRoom" -> ~dropped /\ DropRoom
           [] e.a = "PublishOpen" -> PublishOpen
           [] e.a = "Event" -> Event(e.m)
           [] e.a = "DropPipeline" -> DropPipeline
           [] e.a = "Hash" -> Hash(e.g)
           [] e.a = "Release" -> Release(e.g)
           [] e.a = "Complete" -> Complete(e.g)

TNext == \/ /\ j < Len(Traces[t]) /\ Do(Traces[t][j + 1]) /\ j' = j + 1 /\ UNCHANGED t
         \/ /\ j = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == j = Len(Traces[t]) => dropped /\ \A m \in M : msg[m].pc = "taken"
=============================================================================
