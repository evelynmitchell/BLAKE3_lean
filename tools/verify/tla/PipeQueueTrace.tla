---------------------------- MODULE PipeQueueTrace ----------------------------
(* Trace validation of PipeQueue.tla's queue against threads/src/source.rs:
   every schedule Shuttle runs of tests/shuttle_source.rs (the owner
   publishing a slot's two tasks, a piece's action and a group's, then
   waiting for them, running waiting actions itself or not; one worker
   taking, running, and parking behind its bit) is logged, and check.py
   turns each log into the PipeQueue.tla actions it is (`Traces`). One the
   model does not allow leaves no step, a deadlock TLC reports with the
   trace. A trace taken whole ends with the owner finished (Ends). *)
EXTENDS PipeQueue

CONSTANT Traces

VARIABLES t, j
tvars == <<vars, t, j>>

\* The executor is the trace's (its first step names it).
TInit == Init /\ t \in 1..Len(Traces) /\ j = 0 /\ blockOn = Traces[t][1].block

\* A worker's look again after its bit: Recheck, unless a wake has sent it
\* looking already (the stand-in's wake clears the bit, as the model's).
Settle(w) == \/ wpc[w] = "bit" /\ Recheck(w)
             \/ wpc[w] = "look" /\ UNCHANGED vars

Do(e) == CASE e.a = "Mode" -> blockOn = e.block /\ UNCHANGED vars
           [] e.a = "Tasks" -> TasksN(e.n)
           [] e.a = "Piece" -> ShortPiece
           [] e.a = "Group" -> Group
           [] e.a = "Look" -> Look(e.w)
           [] e.a = "Claim" -> Claim(e.w)
           [] e.a = "Run" -> Run(e.w)
           [] e.a = "Settle" -> Settle(e.w)
           [] e.a = "StartWait" -> StartWait
           [] e.a = "ORead" -> ORead
           [] e.a = "OClaim" -> OClaim
           [] e.a = "ORun" -> ORun
           [] e.a = "Sleep" -> Sleep
           [] e.a = "SleepCheck" -> SleepCheck
           [] e.a = "PubWake" -> PubWake
           [] e.a = "Woken" -> Woken
           [] e.a = "Finish" -> Finish

TNext == \/ /\ j < Len(Traces[t]) /\ Do(Traces[t][j + 1]) /\ j' = j + 1 /\ UNCHANGED t
         \/ /\ j = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == j = Len(Traces[t]) => opc = "done"
=============================================================================
