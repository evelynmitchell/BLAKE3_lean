--------------------------------- MODULE MCPark ---------------------------------
(* Park's model: three workers, one wake a hop (so most wakes are owed and
   paid by woken workers), batches of 3, 1 and 2 pieces. *)
EXTENDS Park
MCBatches == <<3, 1, 2>>
=============================================================================
