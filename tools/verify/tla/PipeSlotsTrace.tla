---------------------------- MODULE PipeSlotsTrace ----------------------------
(* Trace validation of PipeSlots.tla against threads/src/pipeline.rs: every
   schedule Shuttle runs of tests/shuttle_pipeline.rs's
   messages_take_slots_and_come_out_in_end_order (in two slots: a message
   lent long, in parts, and one lent short, in a group; their events, the
   owner waiting where none is ready; then a third message in a freed slot,
   aborted while empty, and its event) is logged: the scenario's own calls,
   and the atomic operations that finish each message's work. check.py
   turns each log into the PipeSlots.tla actions it is (`Traces`). One the
   model does not allow leaves no step, a deadlock TLC reports with the
   trace. A trace taken whole ends with the owner finished (Ends). *)
EXTENDS PipeSlots

CONSTANT Traces

VARIABLES t, j
tvars == <<vars, t, j>>

TInit == Init /\ t \in 1..Len(Traces) /\ j = 0

\* The slot message m is in.
SlotOf(m) == CHOOSE s \in S : slot[s].msg = m
\* An owner's call on message m's slot (OnSlot's, with its choices named).
Lent(m, long, early) == cpc = "idle" /\ SliceE(SlotOf(m), long, early) /\ UNCHANGED <<free, events, taken, opened, cpc>>
Aborts(m) == cpc = "idle" /\ Abort(SlotOf(m)) /\ UNCHANGED <<free, events, taken, opened, cpc>>

Do(e) == CASE e.a = "Message1" -> Message1
           [] e.a = "Lent" -> Lent(e.m, e.long, e.early)
           [] e.a = "Abort" -> Aborts(e.m)
           [] e.a = "Ready1" -> Ready1
           [] e.a = "Ready2" -> Ready2
           [] e.a = "ReadyWake" -> ReadyWake
           [] e.a = "NextEvent" -> NextEvent
           [] e.a = "RunTasks" -> RunTasks(e.m)
           [] e.a = "RunGroup" -> RunGroup(e.g)
           [] e.a = "Finish" -> Finish

TNext == \/ /\ j < Len(Traces[t]) /\ Do(Traces[t][j + 1]) /\ j' = j + 1 /\ UNCHANGED t
         \/ /\ j = Len(Traces[t]) /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars

Ends == j = Len(Traces[t]) => cpc = "finished"
=============================================================================
