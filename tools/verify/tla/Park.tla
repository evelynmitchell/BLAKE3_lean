---------------------------------- MODULE Park ----------------------------------
(* threads/src/park.rs: the pool's park and wake. A worker with no work sets
   its parked bit, looks once more, then parks until a waker clears the bit
   (park_unless); a publisher publishes work, then wakes workers for it:
   up to `Fanout` now, the rest owed, which each woken worker pays, up to
   `Fanout` wakes, before it works (wake_for, pay_owed). The owed word packs
   a generation and a count, so a worker retiring debt it could not pay
   cannot wipe out debt a publisher added meanwhile.

   Each action is one atomic operation of the Rust (all SeqCst), except
   wake_one, one step here: its loop (load the bits, clear one with
   fetch_and, retry if another waker took it) ends with one bit cleared by
   this thread, or none set. Work is a count of pieces; `Batches` are what
   the publisher publishes in turn.

   With `Leave`, the workers also leave once every piece is taken, as in
   threads/tests/shuttle_park.rs: the one that takes the last piece wakes
   one more worker, a worker that finds all taken leaves, and that counts
   as work to see (so a parking worker re-checks it). Then every worker
   must leave: a wake spent on a worker that was leaving anyway, and not
   passed on, strands the other in park, which Shuttle found
   (October 23). *)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Workers, Fanout, Batches, Leave

W == 1..Workers

VARIABLES work, taken, parked, token, owedGen, owedCount, spent,
          wpc, cur, made,           \* each worker's place, its read of owed, its wakes paid
          ppc, batch, nowLeft,      \* the publisher's place, batch, wakes left to make
          seenParked                \* the parked count wake_for read

vars == <<work, taken, parked, token, owedGen, owedCount, spent, wpc, cur, made, ppc, batch, nowLeft, seenParked>>

Min(a, b) == IF a < b THEN a ELSE b
ParkedCount == Cardinality({w \in W : parked[w]})

Init == /\ work = 0 /\ taken = 0
        /\ parked = [w \in W |-> FALSE] /\ token = [w \in W |-> FALSE]
        /\ owedGen = 0 /\ owedCount = 0 /\ spent = [w \in W |-> FALSE]
        /\ wpc = [w \in W |-> "look"] /\ cur = [w \in W |-> <<0, 0>>] /\ made = [w \in W |-> 0]
        /\ ppc = "publish" /\ batch = 1 /\ nowLeft = 0 /\ seenParked = 0

(* wake_one: clear one set bit and unpark its worker (Woke(u)); with none set,
   nothing (NoneParked).
   `spent` is a ghost: a wake that cleared the bit of a worker still looking
   (it set its bit and has not parked), until the wake has done its work. *)
Woke(u) == /\ parked[u] /\ parked' = [parked EXCEPT ![u] = FALSE] /\ token' = [token EXCEPT ![u] = TRUE]
           /\ spent' = [spent EXCEPT ![u] = wpc[u] \in {"visible", "clearown"}]
NoneParked == /\ \A u \in W : ~parked[u] /\ UNCHANGED <<parked, token, spent>>

(* Worker w *)
Total == LET F[i \in 0..Len(Batches)] == IF i = 0 THEN 0 ELSE F[i - 1] + Batches[i] IN F[Len(Batches)]
AllDone == Leave /\ taken = Total

Look(w) ==    /\ wpc[w] = "look"
              /\ IF work > 0
                 THEN /\ work' = work - 1 /\ taken' = taken + 1
                      /\ wpc' = IF Leave /\ taken + 1 = Total THEN [wpc EXCEPT ![w] = "lastwake"] ELSE wpc
                 ELSE /\ wpc' = [wpc EXCEPT ![w] = IF AllDone THEN "gone" ELSE "setbit"]
                      /\ UNCHANGED <<work, taken>>
              /\ UNCHANGED <<parked, token, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
\* The last piece's taker: wake one more, to leave too.
LastWake(w) == /\ wpc[w] = "lastwake"
               /\ ((\E u \in W : Woke(u)) \/ NoneParked)
               /\ wpc' = [wpc EXCEPT ![w] = "look"]
               /\ UNCHANGED <<work, taken, owedGen, owedCount, cur, made, ppc, batch, nowLeft, seenParked>>
SetBit(w) ==  /\ wpc[w] = "setbit"
              /\ parked' = [parked EXCEPT ![w] = TRUE] /\ wpc' = [wpc EXCEPT ![w] = "visible"]
              /\ UNCHANGED <<work, taken, token, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
Visible(w) == /\ wpc[w] = "visible"
              /\ wpc' = [wpc EXCEPT ![w] = IF work > 0 \/ AllDone THEN "clearown" ELSE "park"]
              /\ UNCHANGED <<work, taken, parked, token, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
\* Work seen: clear the bit. If a waker cleared it first, pass its wake on.
ClearOwn(w) == /\ wpc[w] = "clearown"
               /\ parked' = [parked EXCEPT ![w] = FALSE]
               /\ wpc' = [wpc EXCEPT ![w] = IF parked[w] THEN "look" ELSE "passon"]
               /\ UNCHANGED <<work, taken, token, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
PassOn(w) ==  /\ wpc[w] = "passon"
              /\ \/ \E u \in W : /\ parked[u] /\ parked' = [parked EXCEPT ![u] = FALSE]
                                 /\ token' = [token EXCEPT ![u] = TRUE]
                                 /\ spent' = [spent EXCEPT ![w] = FALSE, ![u] = wpc[u] \in {"visible", "clearown"}]
                 \/ /\ \A u \in W : ~parked[u] /\ UNCHANGED <<parked, token>>
                    /\ spent' = [spent EXCEPT ![w] = FALSE]
              /\ wpc' = [wpc EXCEPT ![w] = "payload"]
              /\ made' = [made EXCEPT ![w] = 0]
              /\ UNCHANGED <<work, taken, owedGen, owedCount, cur, ppc, batch, nowLeft, seenParked>>
\* while the bit is set: park. The load of the bit (ParkLoad), then the
\* park (ParkWait), which takes the token an unpark left (one left between
\* the load and the park makes it return at once), then the load again. A
\* park may also return with no token (Spurious, as std's and Shuttle's
\* may): no fairness rests on it.
ParkLoad(w) == /\ wpc[w] = "park"
               /\ IF parked[w]
                  THEN wpc' = [wpc EXCEPT ![w] = "parked"] /\ UNCHANGED <<made, spent>>
                  ELSE /\ wpc' = [wpc EXCEPT ![w] = "payload"] /\ made' = [made EXCEPT ![w] = 0]
                       /\ spent' = [spent EXCEPT ![w] = FALSE]     \* runs as woken
               /\ UNCHANGED <<work, taken, parked, token, owedGen, owedCount, cur, ppc, batch, nowLeft, seenParked>>
ParkWait(w) == /\ wpc[w] = "parked" /\ token[w]
               /\ token' = [token EXCEPT ![w] = FALSE] /\ wpc' = [wpc EXCEPT ![w] = "park"]
               /\ UNCHANGED <<work, taken, parked, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
Spurious(w) == /\ wpc[w] = "parked"
               /\ wpc' = [wpc EXCEPT ![w] = "park"]
               /\ UNCHANGED <<work, taken, parked, token, owedGen, owedCount, spent, cur, made, ppc, batch, nowLeft, seenParked>>
\* pay_owed: up to Fanout wakes of the owed count.
PayLoad(w) == /\ wpc[w] = "payload"
              /\ cur' = [cur EXCEPT ![w] = <<owedGen, owedCount>>]
              /\ wpc' = [wpc EXCEPT ![w] = IF made[w] < Fanout /\ owedCount > 0 THEN "paycas" ELSE "look"]
              /\ UNCHANGED <<work, taken, parked, token, owedGen, owedCount, spent, made, ppc, batch, nowLeft, seenParked>>
PayCas(w) ==  /\ wpc[w] = "paycas"
              /\ IF <<owedGen, owedCount>> = cur[w]
                 THEN owedCount' = owedCount - 1 /\ wpc' = [wpc EXCEPT ![w] = "paywake"]
                 ELSE wpc' = [wpc EXCEPT ![w] = "payload"] /\ UNCHANGED owedCount
              /\ UNCHANGED <<work, taken, parked, token, owedGen, spent, cur, made, ppc, batch, nowLeft, seenParked>>
PayWake(w) == /\ wpc[w] = "paywake"
              /\ \/ (\E u \in W : Woke(u)) /\ wpc' = [wpc EXCEPT ![w] = "payload"] /\ made' = [made EXCEPT ![w] = made[w] + 1]
                 \/ NoneParked /\ wpc' = [wpc EXCEPT ![w] = "payclear"] /\ UNCHANGED made
              /\ UNCHANGED <<work, taken, owedGen, owedCount, cur, ppc, batch, nowLeft, seenParked>>
\* No one to wake: retire the debt, only if no publisher added since.
PayClear(w) == /\ wpc[w] = "payclear"
               /\ IF <<owedGen, owedCount>> = <<cur[w][1], cur[w][2] - 1>> THEN owedCount' = 0 ELSE UNCHANGED owedCount
               /\ wpc' = [wpc EXCEPT ![w] = "look"]
               /\ UNCHANGED <<work, taken, parked, token, owedGen, spent, cur, made, ppc, batch, nowLeft, seenParked>>

(* The publisher: publish a batch, then wake_for it. *)
Publish ==    /\ ppc = "publish" /\ batch <= Len(Batches)
              /\ work' = work + Batches[batch] /\ ppc' = "wake"
              /\ UNCHANGED <<taken, parked, token, owedGen, owedCount, spent, wpc, cur, made, batch, nowLeft, seenParked>>
\* wake_for: read the parked count (parked_count), then owe what is not
\* woken now (the owed word's compare-and-swap loop, one step: it retries
\* until it adds).
WakeFor ==    /\ ppc = "wake"
              /\ seenParked' = ParkedCount /\ ppc' = "owe"
              /\ UNCHANGED <<work, taken, parked, token, owedGen, owedCount, spent, wpc, cur, made, batch, nowLeft>>
WakeOwed ==   /\ ppc = "owe"
              /\ LET need == Min(IF Batches[batch] > Workers - seenParked THEN Batches[batch] - (Workers - seenParked) ELSE 0, seenParked)
                     now == Min(need, Fanout)
                 IN /\ nowLeft' = now
                    /\ IF need > now THEN owedGen' = owedGen + 1 /\ owedCount' = owedCount + (need - now)
                                     ELSE UNCHANGED <<owedGen, owedCount>>
              /\ ppc' = "wakeone"
              /\ UNCHANGED <<work, taken, parked, token, spent, wpc, cur, made, batch, seenParked>>
WakeNow ==    /\ ppc = "wakeone"
              /\ IF nowLeft = 0
                 THEN ppc' = "publish" /\ batch' = batch + 1 /\ UNCHANGED <<parked, token, spent, nowLeft, seenParked>>
                 ELSE \/ (\E u \in W : Woke(u)) /\ nowLeft' = nowLeft - 1 /\ UNCHANGED <<ppc, batch>>
                      \/ NoneParked /\ ppc' = "publish" /\ batch' = batch + 1 /\ UNCHANGED nowLeft
              /\ UNCHANGED <<work, taken, owedGen, owedCount, wpc, cur, made, seenParked>>

Worker(w) == Look(w) \/ LastWake(w) \/ SetBit(w) \/ Visible(w) \/ ClearOwn(w) \/ PassOn(w) \/ ParkLoad(w) \/ ParkWait(w)
             \/ PayLoad(w) \/ PayCas(w) \/ PayWake(w) \/ PayClear(w)
Publisher == Publish \/ WakeFor \/ WakeOwed \/ WakeNow
Next == Publisher \/ \E w \in W : Worker(w) \/ Spurious(w)
Spec == Init /\ [][Next]_vars /\ WF_vars(Publisher) /\ \A w \in W : WF_vars(Worker(w))

(* No wake is lost: every piece published is taken. *)
AllTaken == <>(taken = Total)
(* A wake that reached a worker still looking is not lost: the worker runs as
   woken (it found no work, parked, and finds its bit cleared) or, having found
   work, passes the wake on (park_unless's "Pass the wake on"). *)
WakesPassedOn == \A w \in W : spent[w] => wpc[w] \in {"visible", "clearown", "passon", "park", "parked"}
(* With Leave: every worker leaves, none stranded in park. *)
AllLeave == <>(\A w \in W : wpc[w] = "gone")
TypeOK == work + taken <= Total
=============================================================================
