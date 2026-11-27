--------------------------------- MODULE Waker ---------------------------------
(* threads/src/waker.rs: the Pipeline's single-waiter slot (WakerSlot). The
   caller runs a `Script` of steps. A "wait" is a wait for an item: the
   caller first checks whether it is done (and if so takes it, with no
   clear: Pipeline::poll_ready, poll_room); else it registers its Waker,
   re-checks, and if then done clears and takes it, or waits to be woken.
   A "register" registers a new Waker (another poll's), and a "clear"
   clears. A worker marks each item done, then looks at the slot
   (notify_after_seqcst) and, if a Waker is registered, takes it, stores
   IDLE and wakes it (wake_slow). `Others` threads only notify, with
   nothing done (as tests/shuttle_waker.rs's second thread). A script with
   no wait has no worker.

   register (install_waker) tries REGISTERED -> WRITING first and compares
   the Waker there with its own (will_wake: a wait's is the one before,
   a register's is new), storing REGISTERED back; failing that (the slot IDLE, or WAKING), it
   loads the state until IDLE or REGISTERED and moves it to WRITING, puts
   its Waker in, and stores REGISTERED. clear moves REGISTERED -> WRITING,
   takes the Waker and stores IDLE. The cell is touched only between a
   thread's move to WRITING or WAKING and its store after (`incell`).

   Each action is one atomic operation (all SeqCst; register's fence is
   subsumed), the cell's use one step. *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Script, Others

Rounds == Cardinality({k \in 1..Len(Script) : Script[k] = "wait"})
N == (IF Rounds = 0 THEN 1 ELSE 0)..Others   \* notifiers: 0 the worker, the rest only notify
CALLER == Others + 1   \* the caller, in `incell`

VARIABLES state,    \* "idle", "writing", "registered", "waking"
          cell,     \* the stored Waker: 0 none, k the caller's k-th
          step,     \* the caller's step in its script
          mine,     \* the caller's Waker
          incell,   \* the threads touching the cell
          done,     \* items finished
          seen,     \* items the caller has seen finished
          woken,    \* the caller's Waker was woken (a pending wake)
          cpc,      \* the caller's place
          npc, had  \* each notifier's place; whether its wake_slow took a Waker

vars == <<state, cell, step, mine, incell, done, seen, woken, cpc, npc, had>>

Init == /\ state = "idle" /\ cell = 0 /\ step = 1 /\ mine = 1 /\ incell = {} /\ done = 0 /\ seen = 0
        /\ woken = FALSE /\ cpc = "check"
        /\ npc = [n \in N |-> IF n = 0 THEN "finish" ELSE "notify"] /\ had = [n \in N |-> FALSE]

CallerOnly == UNCHANGED <<done, npc, had>>
Mine == UNCHANGED mine
Wait == Script[step] = "wait"
\* A register's or clear's step done, or a wait's item taken: the next step.
Stepped == step' = step + 1 /\ cpc' = "check"
\* After registering: a wait re-checks its item; a register is done.
Registered == IF Wait THEN cpc' = "recheck" /\ UNCHANGED step ELSE Stepped
\* After clearing: a wait takes its item; a clear is done.
Cleared == IF Wait THEN cpc' = "got" /\ UNCHANGED step ELSE Stepped

(* The caller *)
\* A step begins: a wait checks its item; a register takes a new Waker.
Check ==      /\ cpc = "check" /\ step <= Len(Script)
              /\ CASE Script[step] = "wait" -> cpc' = (IF done > seen THEN "got" ELSE "fast") /\ Mine
                    [] Script[step] = "register" -> cpc' = "fast" /\ mine' = mine + 1
                    [] Script[step] = "clear" -> cpc' = "clear0" /\ Mine
              /\ UNCHANGED <<state, cell, step, incell, woken, seen>> /\ CallerOnly
\* install_waker's fast path: REGISTERED -> WRITING, compare, store back.
Fast ==       /\ cpc = "fast"
              /\ IF state = "registered"
                 THEN state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "compare"
                 ELSE cpc' = "load" /\ UNCHANGED <<state, incell>>
              /\ UNCHANGED <<cell, step, woken, seen>> /\ Mine /\ CallerOnly
Compare ==    /\ cpc = "compare"
              /\ incell' = incell \ {CALLER}
              \* will_wake: the caller's own Waker is kept; another goes the slow way.
              /\ cpc' = IF cell = mine THEN "fastback" ELSE "fastother"
              /\ UNCHANGED <<state, cell, step, woken, seen>> /\ Mine /\ CallerOnly
FastBack ==   /\ cpc \in {"fastback", "fastother"}
              /\ state' = "registered"
              /\ IF cpc = "fastback" THEN Registered ELSE cpc' = "load" /\ UNCHANGED step
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ Mine /\ CallerOnly
\* The loop: load until IDLE or REGISTERED, then compare-and-swap to WRITING.
Load ==       /\ cpc = "load"
              /\ cpc' = IF state \in {"idle", "registered"} THEN "cas" ELSE "load"
              /\ UNCHANGED <<state, cell, step, incell, woken, seen>> /\ Mine /\ CallerOnly
Cas ==        /\ cpc = "cas"
              /\ IF state \in {"idle", "registered"}
                 THEN state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "put"
                 ELSE cpc' = "load" /\ UNCHANGED <<state, incell>>
              /\ UNCHANGED <<cell, step, woken, seen>> /\ Mine /\ CallerOnly
Put ==        /\ cpc = "put"
              /\ cell' = mine /\ incell' = incell \ {CALLER} /\ cpc' = "putback"
              /\ UNCHANGED <<state, step, woken, seen>> /\ Mine /\ CallerOnly
PutBack ==    /\ cpc = "putback"
              /\ state' = "registered" /\ Registered
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ Mine /\ CallerOnly
\* The completion re-check after publishing interest.
Recheck ==    /\ cpc = "recheck"
              /\ cpc' = IF done > seen THEN "clear0" ELSE "pending"
              /\ UNCHANGED <<state, cell, step, incell, woken, seen>> /\ Mine /\ CallerOnly
\* Pending: woken, the caller looks again.
Wake ==       /\ cpc = "pending" /\ woken
              /\ woken' = FALSE /\ cpc' = "check"
              /\ UNCHANGED <<state, cell, step, incell, seen>> /\ Mine /\ CallerOnly
\* clear: REGISTERED -> WRITING, take the Waker, store IDLE; IDLE: nothing.
Clear0 ==     /\ cpc = "clear0"
              /\ \/ state = "idle" /\ Cleared /\ UNCHANGED <<state, incell>>
                 \/ state = "registered" /\ state' = "writing" /\ incell' = incell \cup {CALLER} /\ cpc' = "clear1" /\ UNCHANGED step
                 \/ state \in {"writing", "waking"} /\ UNCHANGED <<state, incell, cpc, step>>   \* spin
              /\ UNCHANGED <<cell, woken, seen>> /\ Mine /\ CallerOnly
Clear1 ==     /\ cpc = "clear1"
              /\ cell' = 0 /\ incell' = incell \ {CALLER} /\ cpc' = "clear2"
              /\ UNCHANGED <<state, step, woken, seen>> /\ Mine /\ CallerOnly
Clear2 ==     /\ cpc = "clear2"
              /\ state' = "idle" /\ Cleared
              /\ UNCHANGED <<cell, incell, woken, seen>> /\ Mine /\ CallerOnly
Got ==        /\ cpc = "got"
              /\ seen' = seen + 1 /\ Stepped
              /\ UNCHANGED <<state, cell, incell, woken>> /\ Mine /\ CallerOnly

(* Notifier n: the worker finishes an item (a SeqCst operation) first. *)
NOnly == UNCHANGED <<seen, cpc, step, mine>>
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
              /\ cell' = 0 /\ had' = [had EXCEPT ![n] = cell # 0]
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
(* A clear leaves the cell empty: the Waker it took is the caller's to drop
   (the second test's drops), and no wake can reach it. *)
ClearEmpties == (cpc = "check" /\ step > 1 /\ Script[step - 1] = "clear") => cell = 0
(* No wake is lost: the caller sees every item, and ends its script. *)
SeesAll == <>(step > Len(Script))
=============================================================================
