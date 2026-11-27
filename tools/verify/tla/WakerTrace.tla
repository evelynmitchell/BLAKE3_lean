------------------------------ MODULE WakerTrace ------------------------------
(* Trace validation of Waker.tla against threads/src/waker.rs: every
   schedule Shuttle runs of tests/shuttle_waker.rs's two tests (a caller
   waiting for one item, the worker finishing it, and one other thread
   notifying with nothing done; a caller registering two Wakers and
   clearing, one other thread notifying) is logged, and check.py turns each log into
   the Waker.tla actions it is (`Traces`). A behavior starts at any trace
   and takes its actions in turn; one the model does not allow leaves no
   step, a deadlock TLC reports with the trace. A trace taken whole ends
   with the caller's script done and every notifier done (Ends). *)
EXTENDS Waker, Sequences

CONSTANT Traces

VARIABLES t, i
tvars == <<vars, t, i>>

TInit == Init /\ t \in 1..Len(Traces) /\ i = 0

Do(e) == CASE e.a = "Check" -> Check
           [] e.a = "Fast" -> Fast
           [] e.a = "Compare" -> Compare
           [] e.a = "FastBack" -> FastBack
           [] e.a = "Load" -> Load
           [] e.a = "Cas" -> Cas
           [] e.a = "Put" -> Put
           [] e.a = "PutBack" -> PutBack
           [] e.a = "Recheck" -> Recheck
           [] e.a = "Wake" -> Wake
           [] e.a = "Clear0" -> Clear0
           [] e.a = "Clear1" -> Clear1
           [] e.a = "Clear2" -> Clear2
           [] e.a = "Got" -> Got
           [] e.a = "Finish" -> Finish(e.n)
           [] e.a = "Notify" -> Notify(e.n)
           [] e.a = "Wake0" -> Wake0(e.n)
           [] e.a = "Wake1" -> Wake1(e.n)
           [] e.a = "Wake2" -> Wake2(e.n)
           [] e.a = "Wake3" -> Wake3(e.n)

TNext == \/ /\ i < Len(Traces[t]) /\ Do(Traces[t][i + 1]) /\ i' = i + 1 /\ UNCHANGED t
         \/ /\ i = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == i = Len(Traces[t]) => step > Len(Script) /\ \A n \in N : npc[n] = "end"
=============================================================================
