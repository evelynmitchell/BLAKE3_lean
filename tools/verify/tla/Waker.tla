--------------------------------- MODULE Waker ---------------------------------
(* threads/src/waker.rs: the Pipeline's single-waiter slot (WakerSlot). A
   caller waiting for an item registers its Waker, then re-checks whether the
   item is done; a worker marks the item done, then looks at the slot and,
   if a Waker is registered, takes it and wakes the caller. The state word
   moves IDLE -> WRITING -> REGISTERED (register), REGISTERED -> WRITING ->
   IDLE (clear), REGISTERED -> WAKING -> IDLE (wake_slow); the cell holding
   the Waker is touched only by the thread whose compare-and-swap moved the
   state to WRITING or WAKING.

   Each action is one atomic operation of the Rust (all SeqCst; register's
   fence is subsumed). The caller waits `Rounds` times; each round a worker
   finishes one item. `incell` is the set of threads inside the cell. *)
EXTENDS Naturals

CONSTANTS Rounds

VARIABLES state,    \* "idle", "writing", "registered", "waking"
          cell,     \* the stored Waker: "none" or "waker"
          incell,   \* the threads touching the cell
          done,     \* items finished
          seen,     \* items the caller has seen finished
          woken,    \* the caller's Waker was woken (a pending wake)
          cpc, wpc  \* the caller's and the worker's places

vars == <<state, cell, incell, done, seen, woken, cpc, wpc>>

Init == /\ state = "idle" /\ cell = "none" /\ incell = {} /\ done = 0 /\ seen = 0
        /\ woken = FALSE /\ cpc = "check" /\ wpc = "finish"

(* The caller: wait for item seen + 1 (Pipeline::ready). *)
Check ==     /\ cpc = "check" /\ seen < Rounds
             /\ IF done > seen THEN cpc' = "clear0" ELSE cpc' = "reg"
             /\ UNCHANGED <<state, cell, incell, done, seen, woken, wpc>>
\* install_waker: from IDLE or REGISTERED, compare-and-swap to WRITING.
RegLock ==   /\ cpc = "reg" /\ state \in {"idle", "registered"}
             /\ state' = "writing" /\ incell' = incell \cup {"caller"} /\ cpc' = "regwrite"
             /\ UNCHANGED <<cell, done, seen, woken, wpc>>
RegWrite ==  /\ cpc = "regwrite"
             /\ cell' = "waker" /\ incell' = incell \ {"caller"} /\ cpc' = "regstore"
             /\ UNCHANGED <<state, done, seen, woken, wpc>>
RegStore ==  /\ cpc = "regstore"
             /\ state' = "registered" /\ cpc' = "recheck"
             /\ UNCHANGED <<cell, incell, done, seen, woken, wpc>>
\* The completion re-check after publishing interest.
Recheck ==   /\ cpc = "recheck"
             /\ cpc' = IF done > seen THEN "clear0" ELSE "pending"
             /\ UNCHANGED <<state, cell, incell, done, seen, woken, wpc>>
\* Pending: the future returns Pending; the executor polls again once woken.
Wake ==      /\ cpc = "pending" /\ woken
             /\ woken' = FALSE /\ cpc' = "check"
             /\ UNCHANGED <<state, cell, incell, done, seen, wpc>>
\* clear: REGISTERED -> WRITING, take the Waker, store IDLE; IDLE: nothing.
Clear0 ==    /\ cpc = "clear0"
             /\ \/ state = "idle" /\ cpc' = "got" /\ UNCHANGED <<state, incell>>
                \/ state = "registered" /\ state' = "writing" /\ incell' = incell \cup {"caller"} /\ cpc' = "clear1"
             /\ UNCHANGED <<cell, done, seen, woken, wpc>>
Clear1 ==    /\ cpc = "clear1"
             /\ cell' = "none" /\ incell' = incell \ {"caller"} /\ cpc' = "clear2"
             /\ UNCHANGED <<state, done, seen, woken, wpc>>
Clear2 ==    /\ cpc = "clear2"
             /\ state' = "idle" /\ cpc' = "got"
             /\ UNCHANGED <<cell, incell, done, seen, woken, wpc>>
Got ==       /\ cpc = "got"
             /\ seen' = seen + 1 /\ cpc' = "check"
             /\ UNCHANGED <<state, cell, incell, done, woken, wpc>>

(* The worker: finish an item (a SeqCst operation), then notify_after_seqcst. *)
Finish ==    /\ wpc = "finish" /\ done < Rounds /\ done = seen
             /\ done' = done + 1 /\ wpc' = "notify"
             /\ UNCHANGED <<state, cell, incell, seen, woken, cpc>>
Notify ==    /\ wpc = "notify"
             /\ wpc' = IF state = "registered" THEN "wake0" ELSE "finish"
             /\ UNCHANGED <<state, cell, incell, done, seen, woken, cpc>>
\* wake_slow: REGISTERED -> WAKING, take the Waker, store IDLE, wake it.
Wake0 ==     /\ wpc = "wake0"
             /\ IF state = "registered"
                THEN state' = "waking" /\ incell' = incell \cup {"worker"} /\ wpc' = "wake1"
                ELSE wpc' = "finish" /\ UNCHANGED <<state, incell>>
             /\ UNCHANGED <<cell, done, seen, woken, cpc>>
Wake1 ==     /\ wpc = "wake1"
             /\ cell' = "none" /\ incell' = incell \ {"worker"} /\ wpc' = "wake2"
             /\ woken' = (cell = "waker" \/ woken)
             /\ UNCHANGED <<state, done, seen, cpc>>
Wake2 ==     /\ wpc = "wake2"
             /\ state' = "idle" /\ wpc' = "finish"
             /\ UNCHANGED <<cell, incell, done, seen, woken, cpc>>

Caller == Check \/ RegLock \/ RegWrite \/ RegStore \/ Recheck \/ Wake \/ Clear0 \/ Clear1 \/ Clear2 \/ Got
Worker == Finish \/ Notify \/ Wake0 \/ Wake1 \/ Wake2
Next == Caller \/ Worker
Spec == Init /\ [][Next]_vars /\ WF_vars(Caller) /\ WF_vars(Worker)

(* One thread at a time in the cell. *)
CellExclusive == incell \in {{}, {"caller"}, {"worker"}}
(* The caller sees an item finished only once it is. *)
SeesOnlyDone == seen <= done
(* No wake is lost: the caller sees every item. *)
SeesAll == <>(seen = Rounds)
=============================================================================
