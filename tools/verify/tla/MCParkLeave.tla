------------------------------ MODULE MCParkLeave ------------------------------
(* Park's model with the workers leaving at the end (Leave), as
   threads/tests/shuttle_park.rs's run: two workers, one wake a hop, a
   publisher of two batches of one piece. *)
EXTENDS Park
MCBatches == <<1, 1>>
=============================================================================
