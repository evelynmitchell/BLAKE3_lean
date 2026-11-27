---------------------------- MODULE PipeTasksTrace ----------------------------
(* Trace validation of PipeTasks.tla against threads/src/pipeline.rs: every
   schedule Shuttle runs of tests/shuttle_pipeline.rs's
   lent_parts_and_a_group (a message lent and hashed in three parts, then
   two short ones lent in one group; each guard dropped at its event) is
   logged, an atomic operation a step, and check.py turns each log into the
   PipeTasks.tla actions it is (`Traces`). One the model does not allow
   leaves no step, a deadlock TLC reports with the trace. A trace taken
   whole ends with both events taken (Ends). *)
EXTENDS PipeTasks

CONSTANT Traces

VARIABLES t, i
tvars == <<vars, t, i>>

TInit == Init /\ t \in 1..Len(Traces) /\ i = 0

Do(e) == CASE e.a = "Wait" -> Wait
           [] e.a = "Check" -> Check
           [] e.a = "Clear" -> Clear
           [] e.a = "Woken" -> Woken
           [] e.a = "Repoll" -> Repoll
           [] e.a = "TakeMsg" -> TakeMsg
           [] e.a = "TakeGroup" -> TakeGroup
           [] e.a = "Write" -> Write(e.p)
           [] e.a = "Count" -> Count(e.p)
           [] e.a = "Fold" -> Fold(e.p)
           [] e.a = "Loan" -> Loan(e.p)
           [] e.a = "PublishSlot" -> PublishSlot(e.p)
           [] e.a = "RunMembers" -> RunMembers
           [] e.a = "Complete" -> Complete

TNext == \/ /\ i < Len(Traces[t]) /\ Do(Traces[t][i + 1]) /\ i' = i + 1 /\ UNCHANGED t
         \/ /\ i = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == i = Len(Traces[t]) => opc = "finished"
=============================================================================
