---------------------------------- MODULE Turn ----------------------------------
(* threads/src/lanes.rs, sources::run_one: how workers choose among the
   registered sources. A worker takes from the lowest-slot source that has
   an item (find_from from 0); after every `TURN` items it takes one in
   turn: its walk starts at its cursor, and the cursor moves past the slot
   it served (Turn { taken, cursor }), so every source gets a share of
   every worker that its slot does not decide.

   Slot 1 holds a Pipeline that streams: it always has an item (it
   publishes its next before its last is taken). Slots 2..Sources hold
   `Items` each, waiting. Each worker step is one run_one; each claim is
   one compare-and-swap on the source (take), here one step. *)
EXTENDS Naturals

CONSTANTS Sources, Workers, TURN, Items

S == 1..Sources
W == 1..Workers

VARIABLES left,       \* items waiting in each source 2..Sources (slot 1 streams)
          taken,      \* each worker's count toward its next turn
          cursor      \* each worker's start for its next turn

vars == <<left, taken, cursor>>

Init == /\ left = [s \in S |-> IF s = 1 THEN 0 ELSE Items]
        /\ taken = [w \in W |-> 0] /\ cursor = [w \in W |-> 1]

HasItem(s) == s = 1 \/ left[s] > 0
\* The walk from `start` up, then the slots below it (find_from).
Order(start) == [k \in 1..Sources |-> ((start - 1 + k - 1) % Sources) + 1]
First(start) == LET o == Order(start)
                    ks == {k \in 1..Sources : HasItem(o[k])}
                IN o[CHOOSE k \in ks : \A j \in ks : k <= j]

RunOne(w) ==
  LET inTurn == taken[w] >= TURN
      start == IF inTurn THEN cursor[w] ELSE 1
      s == First(start)
  IN /\ left' = IF s = 1 THEN left ELSE [left EXCEPT ![s] = left[s] - 1]
     /\ IF inTurn
        THEN taken' = [taken EXCEPT ![w] = 0] /\ cursor' = [cursor EXCEPT ![w] = (s % Sources) + 1]
        ELSE taken' = [taken EXCEPT ![w] = taken[w] + 1] /\ UNCHANGED cursor

Next == \E w \in W : RunOne(w)
Spec == Init /\ [][Next]_vars /\ \A w \in W : WF_vars(RunOne(w))

(* No source starves behind one that streams: every item waiting is taken. *)
NoneStarves == \A s \in 2..Sources : <>(left[s] = 0)
=============================================================================
