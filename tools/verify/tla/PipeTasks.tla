------------------------------- MODULE PipeTasks -------------------------------
(* threads/src/pipeline.rs: messages hashed in parts, loans, and groups.

   A message (or a batch) over more than one piece is `Parts` tasks; each
   writes its piece's value and counts itself off (tasks_left fetch_sub);
   the one that counts the last off folds the values into the hash, marks
   a loan complete (loan_completed), then publishes the slot done and wakes
   the owner (run_multi_piece, finished). The message here is lent
   (Pipeline::lent): the owner may drop its Lent guard once its event is
   taken, and a guard dropped before the loan is marked complete stops the
   process (Lent::drop). Short messages share a group: one task hashes the
   group's `Members`, then publishes the group's epoch complete and wakes
   the owner (run_group).

   The owner ends both, waits (the WakerSlot's contract, as PipeRooms.tla:
   a re-check that finds the event ready then clears the Waker, and a wait
   may poll again with no wake, as block_on does), takes the message's
   event and at once drops its guard, then takes the group's events.
   PipeTasksTrace.tla checks this model against the code's schedules. *)
EXTENDS Naturals, Sequences

CONSTANTS Parts, Members

VARIABLES written, left, hashed, loanDone, slotDone,  \* the message's parts, its count, hash, loan, publication
          ppc,                                         \* each part's place
          members, gpc, groupDone,                     \* the group's members hashed, its task's place, publication
          registered, woken, opc,                      \* the owner's WakerSlot and place
          msgEvent, guardDropped, groupEvent           \* what the owner has taken and done

vars == <<written, left, hashed, loanDone, slotDone, ppc, members, gpc, groupDone,
          registered, woken, opc, msgEvent, guardDropped, groupEvent>>

Init == /\ written = [p \in 1..Parts |-> FALSE] /\ left = Parts /\ hashed = "none"
        /\ loanDone = FALSE /\ slotDone = FALSE /\ ppc = [p \in 1..Parts |-> "write"]
        /\ members = [m \in 1..Members |-> FALSE] /\ gpc = "run" /\ groupDone = FALSE
        /\ registered = FALSE /\ woken = FALSE /\ opc = "msg"
        /\ msgEvent = "none" /\ guardDropped = FALSE /\ groupEvent = "none"

Notify == IF registered THEN registered' = FALSE /\ woken' = TRUE ELSE UNCHANGED <<registered, woken>>

OwnerVars == <<registered, woken, opc, msgEvent, guardDropped, groupEvent>>
MsgVars == <<written, left, hashed, loanDone, slotDone, ppc>>
GroupVars == <<members, gpc, groupDone>>

(* A part of the message *)
Write(p) ==   /\ ppc[p] = "write"
              /\ written' = [written EXCEPT ![p] = TRUE] /\ ppc' = [ppc EXCEPT ![p] = "count"]
              /\ UNCHANGED <<left, hashed, loanDone, slotDone>> /\ UNCHANGED GroupVars /\ UNCHANGED OwnerVars
Count(p) ==   /\ ppc[p] = "count"
              /\ left' = left - 1
              /\ ppc' = [ppc EXCEPT ![p] = IF left = 1 THEN "fold" ELSE "end"]
              /\ UNCHANGED <<written, hashed, loanDone, slotDone>> /\ UNCHANGED GroupVars /\ UNCHANGED OwnerVars
\* The last part: fold every value into the hash.
Fold(p) ==    /\ ppc[p] = "fold"
              /\ hashed' = IF \A q \in 1..Parts : written[q] THEN "whole" ELSE "partial"
              /\ ppc' = [ppc EXCEPT ![p] = "loan"]
              /\ UNCHANGED <<written, left, loanDone, slotDone>> /\ UNCHANGED GroupVars /\ UNCHANGED OwnerVars
Loan(p) ==    /\ ppc[p] = "loan"
              /\ loanDone' = TRUE /\ ppc' = [ppc EXCEPT ![p] = "publish"]
              /\ UNCHANGED <<written, left, hashed, slotDone>> /\ UNCHANGED GroupVars /\ UNCHANGED OwnerVars
PublishSlot(p) == /\ ppc[p] = "publish"
                  /\ slotDone' = TRUE /\ ppc' = [ppc EXCEPT ![p] = "end"]
                  /\ Notify
                  /\ UNCHANGED <<written, left, hashed, loanDone>> /\ UNCHANGED GroupVars
                  /\ UNCHANGED <<opc, msgEvent, guardDropped, groupEvent>>

(* The group's task: hash every member, then publish the epoch complete. *)
RunMembers == /\ gpc = "run"
              /\ members' = [m \in 1..Members |-> TRUE] /\ gpc' = "complete"
              /\ UNCHANGED groupDone /\ UNCHANGED MsgVars /\ UNCHANGED OwnerVars
Complete ==   /\ gpc = "complete"
              /\ groupDone' = TRUE /\ gpc' = "end"
              /\ Notify
              /\ UNCHANGED members /\ UNCHANGED MsgVars /\ UNCHANGED <<opc, msgEvent, guardDropped, groupEvent>>

(* The owner: wait for each event in turn (register, re-check, wait for a
   wake), take it; the message's guard is dropped as soon as its event is. *)
Ready(c) == IF c = "msg" THEN slotDone ELSE groupDone
Wait ==       /\ opc \in {"msg", "group"}
              /\ IF Ready(opc) THEN opc' = opc \o "take" /\ UNCHANGED registered
                 ELSE registered' = TRUE /\ opc' = opc \o "check"
              /\ UNCHANGED <<woken, msgEvent, guardDropped, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
Check ==      /\ opc \in {"msgcheck", "groupcheck"}
              /\ LET c == IF opc = "msgcheck" THEN "msg" ELSE "group"
                 IN opc' = IF Ready(c) THEN c \o "clear" ELSE c \o "wait"
              /\ UNCHANGED <<registered, woken, msgEvent, guardDropped, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
\* Found it ready: the Waker cleared (WakerSlot::clear), after.
Clear ==      /\ opc \in {"msgclear", "groupclear"}
              /\ registered' = FALSE /\ opc' = IF opc = "msgclear" THEN "msgtake" ELSE "grouptake"
              /\ UNCHANGED <<woken, msgEvent, guardDropped, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
\* A wait polled again with no wake (block_on polls once more before it
\* sleeps). Outside the fairness assumption: no liveness rests on it.
Repoll ==     /\ opc \in {"msgwait", "groupwait"}
              /\ opc' = IF opc = "msgwait" THEN "msg" ELSE "group"
              /\ UNCHANGED <<registered, woken, msgEvent, guardDropped, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
Woken ==      /\ opc \in {"msgwait", "groupwait"} /\ woken
              /\ woken' = FALSE /\ opc' = IF opc = "msgwait" THEN "msg" ELSE "group"
              /\ UNCHANGED <<registered, msgEvent, guardDropped, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
TakeMsg ==    /\ opc = "msgtake"
              /\ msgEvent' = hashed /\ guardDropped' = TRUE /\ opc' = "group"
              /\ UNCHANGED <<registered, woken, groupEvent>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars
TakeGroup ==  /\ opc = "grouptake"
              /\ groupEvent' = IF \A m \in 1..Members : members[m] THEN "whole" ELSE "partial"
              /\ opc' = "finished"
              /\ UNCHANGED <<registered, woken, msgEvent, guardDropped>> /\ UNCHANGED MsgVars /\ UNCHANGED GroupVars

Owner == Wait \/ Check \/ Clear \/ Woken \/ TakeMsg \/ TakeGroup
Part(p) == Write(p) \/ Count(p) \/ Fold(p) \/ Loan(p) \/ PublishSlot(p)
Group == RunMembers \/ Complete
Next == Owner \/ Repoll \/ Group \/ \E p \in 1..Parts : Part(p)
Spec == Init /\ [][Next]_vars /\ WF_vars(Owner) /\ WF_vars(Group) /\ \A p \in 1..Parts : WF_vars(Part(p))

(* An event carries a hash of every part (every member): none is published
   before its last value is in. *)
EventsWhole == /\ msgEvent \in {"none", "whole"}
               /\ groupEvent \in {"none", "whole"}
(* A Lent guard is dropped only with its loan complete: no worker reads the
   lent bytes after (Lent::drop does not stop the process). *)
LoanSafe == guardDropped => loanDone
(* No wake is lost: the owner takes both events. *)
Finishes == <>(opc = "finished")
=============================================================================
