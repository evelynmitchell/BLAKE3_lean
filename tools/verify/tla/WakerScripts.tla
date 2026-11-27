----------------------------- MODULE WakerScripts -----------------------------
(* The caller's scripts Waker.tla is checked with: three waits for items;
   one wait (tests/shuttle_waker.rs's first test); and its second test's
   register, register again (another Waker), clear. *)
Waits == <<"wait", "wait", "wait">>
OneWait == <<"wait">>
Swap == <<"register", "register", "clear">>
=============================================================================
