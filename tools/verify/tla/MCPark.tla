--------------------------------- MODULE MCPark ---------------------------------
(* Park's model: three workers, one wake a hop (so most wakes are owed and
   paid by woken workers), batches of 2 and 1 pieces. *)
EXTENDS Park
MCBatches == <<2, 1>>
=============================================================================
