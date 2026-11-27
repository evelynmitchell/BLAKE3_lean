------------------------------ MODULE FinishTrace ------------------------------
(* Trace validation of Finish.tla against threads/src/finish.rs: every
   schedule Shuttle runs in tests/shuttle_finish.rs is logged, operation by
   operation, and check.py turns each log into the Finish.tla actions it is
   (`Traces`, in a module check.py writes). Here a behavior starts at any one
   trace and takes its actions in turn, each as the model's own action. A
   trace with an operation the model does not allow at that point leaves no
   step: TLC reports it as a deadlock, with the trace. A trace taken whole
   ends with the caller returned and every finisher done (Ends). *)
EXTENDS Finish, Sequences

CONSTANT Traces

VARIABLES t, i
tvars == <<vars, t, i>>

TInit == Init /\ t \in 1..Len(Traces) /\ i = 0

Do(e) == CASE e.a = "Poll" -> Poll /\ wpc' = e.to
           [] e.a = "SetBit" -> SetBit
           \* park returns: with the token there it takes it; without, the
           \* return is a spurious wake (Shuttle's park gives them, as std's may).
           [] e.a = "Park" -> IF token THEN Park ELSE SpuriousWake
           [] e.a = "Recheck" -> Recheck
           [] e.a = "Clear" -> Clear
           [] e.a = "Add" -> Add(e.f)
           [] e.a = "Unpark" -> Unpark(e.f)

TNext == \/ /\ i < Len(Traces[t]) /\ Do(Traces[t][i + 1]) /\ i' = i + 1 /\ UNCHANGED t
         \/ /\ i = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == i = Len(Traces[t]) => wpc = "done" /\ \A f \in 1..Finishers : fpc[f] = "done"
=============================================================================
