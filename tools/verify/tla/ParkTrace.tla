------------------------------- MODULE ParkTrace -------------------------------
(* Trace validation of Park.tla against threads/src/park.rs: every schedule
   Shuttle runs of tests/shuttle_park.rs's owed_wakes_cascade (three workers
   that park_unless once and pay what is owed, and a publisher that
   publishes three pieces and calls wake_for(3, 3), with one wake a hop) is
   logged, and check.py turns each log into the Park.tla actions it is
   (`Traces`). The test's workers begin at their bit, not at looking for
   work, and stop when they have paid (Park.tla's "look"), so a behavior
   here begins there. The park loop's loads are ParkLoad, its parks
   returning ParkWait (the token taken) or Spurious. wake_one's loop (a load of the bits, then
   fetch_ands) is one step of the model, taken where the code decides: the
   fetch_and that clears a bit (`u`), or the load or fetch_and that finds
   none (0). A trace the model cannot take
   is a deadlock; a trace taken whole ends with every worker done and the
   publisher's wakes made (Ends). *)
EXTENDS Park

CONSTANT Traces

VARIABLES t, i
tvars == <<vars, t, i>>

TInit == /\ work = 0 /\ taken = 0
         /\ parked = [w \in W |-> FALSE] /\ token = [w \in W |-> FALSE]
         /\ owedGen = 0 /\ owedCount = 0 /\ spent = [w \in W |-> FALSE]
         /\ wpc = [w \in W |-> "setbit"] /\ cur = [w \in W |-> <<0, 0>>] /\ made = [w \in W |-> 0]
         /\ ppc = "publish" /\ batch = 1 /\ nowLeft = 0 /\ seenParked = 0
         /\ t \in 1..Len(Traces) /\ i = 0

\* Which bit a wake_one cleared: worker u's, or none set (0).
WakeSel(u) == IF u = 0 THEN \A x \in W : ~parked[x] ELSE parked[u] /\ ~parked'[u]

Do(e) == CASE e.a = "SetBit" -> SetBit(e.w)
           [] e.a = "Visible" -> Visible(e.w)
           [] e.a = "ClearOwn" -> ClearOwn(e.w)
           [] e.a = "PassOn" -> PassOn(e.w) /\ WakeSel(e.u)
           [] e.a = "ParkLoad" -> ParkLoad(e.w)
           [] e.a = "ParkRet" -> IF token[e.w] THEN ParkWait(e.w) ELSE Spurious(e.w)
           [] e.a = "PayLoad" -> PayLoad(e.w)
           [] e.a = "PayCas" -> PayCas(e.w)
           [] e.a = "PayWake" -> PayWake(e.w) /\ WakeSel(e.u)
           [] e.a = "PayClear" -> PayClear(e.w)
           [] e.a = "Publish" -> Publish
           [] e.a = "WakeFor" -> WakeFor
           [] e.a = "WakeOwed" -> WakeOwed
           [] e.a = "WakeNow" -> WakeNow /\ nowLeft > 0 /\ WakeSel(e.u)
           [] e.a = "WakeEnd" -> WakeNow /\ nowLeft = 0

TNext == \/ /\ i < Len(Traces[t]) /\ Do(Traces[t][i + 1]) /\ i' = i + 1 /\ UNCHANGED t
         \/ /\ i = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == i = Len(Traces[t]) => (\A w \in W : wpc[w] = "look") /\ ppc = "publish"
=============================================================================
