----------------------------- MODULE MCWakerSwap -----------------------------
(* Waker.tla's caller as tests/shuttle_waker.rs's second test: it registers
   one Waker, then another (whose fast path finds the first there, not its
   own), then clears, while another thread notifies. *)
EXTENDS Waker, WakerScripts
=============================================================================
