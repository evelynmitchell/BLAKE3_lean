---------------------------- MODULE MCPipeSlotsOne ----------------------------
(* PipeSlots.tla in a Pipeline of one slot (Limits.messages = 1), where
   message()'s second refusal can be met in few steps: an event waiting
   untaken, the one slot ended behind it, and message() called. *)
EXTENDS PipeSlots
=============================================================================
