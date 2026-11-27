--------------------------------- MODULE Waker ---------------------------------
(* threads/src/waker.rs: the Pipeline's single-waiter slot (WakerSlot). A
   caller waiting for an item first checks whether it is done (and if so
   takes it, with no clear: Pipeline::poll_ready, poll_room); else it
   registers its Waker, re-checks, and if then done clears and takes it, or
   waits to be woken. A worker marks the item done, then looks at the slot
   (notify_after_seqcst) and, if a Waker is registered, takes it, stores
   IDLE and wakes it (wake_slow). `Others` threads only notify, with nothing
   done (as tests/shuttle_waker.rs's second thread).

   register (install_waker) tries REGISTERED -> WRITING first and compares
   the Waker there (will_wake: the caller's is the same one each time),
   storing REGISTERED back; failing that (the slot IDLE, or WAKING), it
   loads the state until IDLE or REGISTERED and moves it to WRITING, puts
   its Waker in, and stores REGISTERED. clear moves REGISTERED -> WRITING,
   takes the Waker and stores IDLE. The cell is touched only between a
   thread's move to WRITING or WAKING and its store after (`incell`).

   Each action is one atomic operation (all SeqCst; register's fence is
   subsumed), the cell's use one step. *)
EXTENDS Naturals

CONSTANTS Rounds, Others

N == 0..Others   \* notifiers: 0 the worker, the rest only notify
CALLER == Others + 1   \* the caller, in `incell`

VARIABLES state,    \* "idle", "writing", "registered", "waking"
          cell,     \* the stored Waker: "none" or "waker"
          incell,   \* the threads touching the cell
          done,     \* items finished
          seen,     \* items the caller has seen finished
          woken,    \* the caller's Waker was woken (a pending wake)
          cpc,      \* the caller's place
          npc, had  \* each notifier's place; whether its wake_slow took a Waker

vars == <<state, cell, incell, done, seen, woken, cpc, npc, had>>

Init == /\ state = "idle" /\ cell = "none" /\ incell = {} /\ done = 0 /\ seen = 0
        /\ woken = FALSE /\ cpc = "check"
        /\ npc = [n \in N |-> IF n = 0 THEN "finish" ELSE "notify"] /\ had = [n \in N |-> FALSE]

CallerOnly == UNCHANGED <<done, npc, had>>

(* The caller *)
Check ==      /\ cpc = "check" /\ seen < Rounds
              /\ cpc' = IF done > seen THEN "got" ELSE "fast"
              /\ UNCHANGED <<state, cell, incell, woken, seen>> /\ CallerOnly
\* install_waker's fast path: REGISTERED -> WRITING, compare, store back.
Fast ==       /\ cpc = "fast"
              /\ IF state = "registered"
                 THEN state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "compare"
                 ELSE cpc' = "load" /\ UNCHANGED <<state, incell>>
              /\ UNCHANGED <<cell, woken, seen>> /\ CallerOnly
Compare ==    /\ cpc = "compare"
              /\ incell' = incell \ {CALLER}
              \* will_wake: the same Waker is kept; another goes the slow way.
              /\ cpc' = IF cell = "waker" THEN "fastback" ELSE "fastother"
              /\ UNCHANGED <<state, cell, woken, seen>> /\ CallerOnly
FastBack ==   /\ cpc \in {"fastback", "fastother"}
              /\ state' = "registered" /\ cpc' = IF cpc = "fastback" THEN "recheck" ELSE "load"
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ CallerOnly
\* The loop: load until IDLE or REGISTERED, then compare-and-swap to WRITING.
Load ==       /\ cpc = "load"
              /\ cpc' = IF state \in {"idle", "registered"} THEN "cas" ELSE "load"
              /\ UNCHANGED <<state, cell, incell, woken, seen>> /\ CallerOnly
Cas ==        /\ cpc = "cas"
              /\ IF state \in {"idle", "registered"}
                 THEN state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "put"
                 ELSE cpc' = "load" /\ UNCHANGED <<state, incell>>
              /\ UNCHANGED <<cell, woken, seen>> /\ CallerOnly
Put ==        /\ cpc = "put"
              /\ cell' = "waker" /\ incell' = incell \ {CALLER} /\ cpc' = "putback"
              /\ UNCHANGED <<state, woken, seen>> /\ CallerOnly
PutBack ==    /\ cpc = "putback"
              /\ state' = "registered" /\ cpc' = "recheck"
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ CallerOnly
\* The completion re-check after publishing interest.
Recheck ==    /\ cpc = "recheck"
              /\ cpc' = IF done > seen THEN "clear0" ELSE "pending"
              /\ UNCHANGED <<state, cell, incell, woken, seen>> /\ CallerOnly
\* Pending: woken, the caller looks again.
Wake ==       /\ cpc = "pending" /\ woken
              /\ woken' = FALSE /\ cpc' = "check"
              /\ UNCHANGED <<state, cell, incell, seen>> /\ CallerOnly
\* clear: REGISTERED -> WRITING, take the Waker, store IDLE; IDLE: nothing.
Clear0 ==     /\ cpc = "clear0"
              /\ \/ state = "idle" /\ cpc' = "got" /\ UNCHANGED <<state, incell>>
                 \/ state = "registered" /\ state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "clear1"
                 \/ state \in {"writing", "waking"} /\ UNCHANGED <<state, incell, cpc>>   \* spin
              /\ UNCHANGED <<cell, woken, seen>> /\ CallerOnly
Clear1 ==     /\ cpc = "clear1"
              /\ cell' = "none" /\ incell' = incell \ {CALLER} /\ cpc' = "clear2"
              /\ UNCHANGED <<state, woken, seen>> /\ CallerOnly
Clear2 ==     /\ cpc = "clear2"
              /\ state' = "idle" /\ cpc' = "got"
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ CallerOnly
Got ==        /\ cpc = "got"
              /\ seen' = seen + 1 /\ cpc' = "check"
              /\ UNCHANGED <<state, cell, incell, woken>> /\ CallerOnly

(* Notifier n: the worker finishes an item (a SeqCst operation) first. *)
NOnly == UNCHANGED <<seen, cpc>>
Finish(n) ==  /\ npc[n] = "finish" /\ done < Rounds /\ done = seen
              /\ done' = done + 1 /\ npc' = [npc EXCEPT ![n] = "notify"]
              /\ UNCHANGED <<state, cell, incell, woken, had>> /\ NOnly
Notify(n) ==  /\ npc[n] = "notify"
              /\ npc' = [npc EXCEPT ![n] = IF state = "registered" THEN "wake0" ELSE "end"]
              /\ UNCHANGED <<state, cell, incell, done, woken, had>> /\ NOnly
\* wake_slow: REGISTERED -> WAKING, take the Waker, store IDLE, wake it.
Wake0(n) ==   /\ npc[n] = "wake0"
              /\ IF state = "registered"
                 THEN state' = "waking" /\ incell' = incell \cup {n} /\ npc' = [npc EXCEPT ![n] = "wake1"]
                 ELSE npc' = [npc EXCEPT ![n] = "end"] /\ UNCHANGED <<state, incell>>
              /\ UNCHANGED <<cell, done, woken, had>> /\ NOnly
Wake1(n) ==   /\ npc[n] = "wake1"
              /\ cell' = "none" /\ had' = [had EXCEPT ![n] = cell = "waker"]
              /\ incell' = incell \ {n} /\ npc' = [npc EXCEPT ![n] = "wake2"]
              /\ UNCHANGED <<state, done, woken>> /\ NOnly
Wake2(n) ==   /\ npc[n] = "wake2"
              /\ state' = "idle" /\ npc' = [npc EXCEPT ![n] = "wake3"]
              /\ UNCHANGED <<cell, incell, done, woken, had>> /\ NOnly
Wake3(n) ==   /\ npc[n] = "wake3"
              /\ woken' = (had[n] \/ woken) /\ npc' = [npc EXCEPT ![n] = "end"]
              /\ UNCHANGED <<state, cell, incell, done, had>> /\ NOnly
\* The worker, done notifying, finishes the next item.
Again ==      /\ npc[0] = "end" /\ done < Rounds
              /\ npc' = [npc EXCEPT ![0] = "finish"]
              /\ UNCHANGED <<state, cell, incell, done, woken, had>> /\ NOnly

Caller == Check \/ Fast \/ Compare \/ FastBack \/ Load \/ Cas \/ Put \/ PutBack \/ Recheck \/ Wake
          \/ Clear0 \/ Clear1 \/ Clear2 \/ Got
Notifier(n) == Finish(n) \/ Notify(n) \/ Wake0(n) \/ Wake1(n) \/ Wake2(n) \/ Wake3(n) \/ (n = 0 /\ Again)
Next == Caller \/ \E n \in N : Notifier(n)
Spec == Init /\ [][Next]_vars /\ WF_vars(Caller) /\ \A n \in N : WF_vars(Notifier(n))

(* One thread at a time in the cell. *)
CellExclusive == \A a, b \in incell : a = b
(* The caller sees an item finished only once it is. *)
SeesOnlyDone == seen <= done
(* No wake is lost: the caller sees every item. *)
SeesAll == <>(seen = Rounds)
=============================================================================
