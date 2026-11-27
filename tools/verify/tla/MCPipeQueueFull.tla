--------------------------- MODULE MCPipeQueueFull ---------------------------
(* PipeQueue.tla small enough that the owner can fill the action ring:
   one slot of one piece, no rooms (two piece nodes), one group, so an
   action ring of 4, and four dispatches. *)
EXTENDS PipeQueue
=============================================================================
