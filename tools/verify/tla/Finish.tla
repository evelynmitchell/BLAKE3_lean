--------------------------------- MODULE Finish ---------------------------------
(* threads/src/finish.rs: a job's finish line. The caller waits for `Target`
   pieces; each of `Finishers` workers finishes one. One word holds the count
   of pieces finished and, in its top bit, whether the caller sleeps:

   - Finish::wait polls, then sets the bit and reads the count in one
     fetch_or (SetBit), parks while the count it has is short (Park, Recheck),
     and clears the bit (Clear);
   - Finish::finished adds its piece and reads the bit in one fetch_add (Add),
     and the one that makes the count complete while the bit is set unparks
     the caller (Unpark).

   Each action below is one atomic operation of the Rust (all SeqCst). std's
   park is a token: an unpark before a park makes the park return at once,
   and a park may also return with no unpark (SpuriousWake, given no
   fairness, so no property rests on it). *)
EXTENDS Naturals

CONSTANTS Finishers, Target

VARIABLES count,     \* the pieces finished (the word's low bits)
          sleeping,  \* the word's top bit
          token,     \* the caller's park token
          have,      \* the count the caller last read
          wpc,       \* the caller's place in wait()
          fpc        \* each finisher's place in finished()

vars == <<count, sleeping, token, have, wpc, fpc>>

ASSUME Target = Finishers

Init == /\ count = 0 /\ sleeping = FALSE /\ token = FALSE /\ have = 0
        /\ wpc = "poll"
        /\ fpc = [f \in 1..Finishers |-> "add"]

(* The caller *)
Poll ==      /\ wpc = "poll"
             /\ IF count >= Target THEN wpc' = "done" ELSE wpc' \in {"poll", "setbit"}
             /\ UNCHANGED <<count, sleeping, token, have, fpc>>
SetBit ==    /\ wpc = "setbit"
             /\ sleeping' = TRUE /\ have' = count            \* one fetch_or
             /\ wpc' = IF count < Target THEN "park" ELSE "clear"
             /\ UNCHANGED <<count, token, fpc>>
Park ==      /\ wpc = "park" /\ token
             /\ token' = FALSE /\ wpc' = "recheck"
             /\ UNCHANGED <<count, sleeping, have, fpc>>
SpuriousWake == /\ wpc = "park" /\ wpc' = "recheck"
                /\ UNCHANGED <<count, sleeping, token, have, fpc>>
Recheck ==   /\ wpc = "recheck"
             /\ have' = count
             /\ wpc' = IF count < Target THEN "park" ELSE "clear"
             /\ UNCHANGED <<count, sleeping, token, fpc>>
Clear ==     /\ wpc = "clear"
             /\ sleeping' = FALSE /\ wpc' = "done"
             /\ UNCHANGED <<count, token, have, fpc>>

(* Finisher f *)
Add(f) ==    /\ fpc[f] = "add"
             /\ count' = count + 1                            \* one fetch_add
             /\ fpc' = [fpc EXCEPT ![f] = IF sleeping /\ count + 1 = Target THEN "unpark" ELSE "done"]
             /\ UNCHANGED <<sleeping, token, have, wpc>>
Unpark(f) == /\ fpc[f] = "unpark"
             /\ token' = TRUE /\ fpc' = [fpc EXCEPT ![f] = "done"]
             /\ UNCHANGED <<count, sleeping, have, wpc>>

Caller == Poll \/ SetBit \/ Park \/ Recheck \/ Clear
Next == Caller \/ SpuriousWake \/ \E f \in 1..Finishers : Add(f) \/ Unpark(f)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Caller)
        /\ \A f \in 1..Finishers : WF_vars(Add(f) \/ Unpark(f))

(* The caller returns only with every piece finished, and leaves the bit clear. *)
ReturnsComplete == wpc = "done" => count >= Target /\ ~sleeping
(* No wake is lost: the caller returns. *)
Returns == <>(wpc = "done")
=============================================================================
