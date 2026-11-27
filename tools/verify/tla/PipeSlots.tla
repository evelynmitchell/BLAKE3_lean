------------------------------- MODULE PipeSlots -------------------------------
(* threads/src/pipeline.rs: the message slots, from message() to the event,
   and the order events come out in. The caller opens `Msgs` messages, one
   after another, in a Pipeline of `Slots` slots (Limits.messages), and
   gives each its bytes one of the ways the code has:

     commit of a short Room   OpenEmpty -> OpenShort (holds the Room's credit)
     commit of a whole Room   OpenEmpty -> OpenRooms, a room piece each
     a wait for a Room        OpenShort -> OpenShortDispatched (into a group)
     end                      OpenEmpty -> WaitSingle (the empty hash)
                              OpenShort, OpenShortDispatched -> WaitSingle
                              OpenRooms -> WaitRoomMulti
     abort                    OpenEmpty, OpenShort, OpenShortDispatched,
                              OpenRooms -> WaitAborted
     owned or lent            OpenEmpty -> WaitSingle (short: a group member)
                              OpenEmpty -> WaitMulti (long: the slot's tasks)
     batch                    OpenEmpty -> WaitBatch (none, small: a group
                              member, or large: the slot's tasks)

   and the end, abort, owned, lent and batch each push the slot on the end
   queue (end_queue). reap takes events off the end queue's front, in order,
   while the front's work is done (try_reap_one), into at most `Slots`
   waiting events (events), freeing each slot (free_slots); next_event takes
   one. A slot's work is the workers': a group of short members (push_member,
   publish_open: a group full at `Members`, or sooner, here nondeterministic,
   as the code's byte limit is), a slot's own tasks (slot_done), or room
   pieces (each holding its Room's credit until a worker has read it).

   The waits: message() (poll_message) and ready() (poll_ready) reap, then
   panic where no wait could end (message: every slot open or `Slots` events
   untaken; ready: nothing ended in flight), then publish the open group if
   the end queue's front is in it (front_uses_open_group), then wait. A wait
   ends when the front's work is done: the WakerSlot's register, re-check and
   notify, which Waker.tla checks, wake it for any work done after the
   re-check, and the front's is what lets the wait return. What is left out:
   the group ring's reuse (acquire_free_group: groups here are never reused),
   a commit after a short one (OpenRooms { sealed }, and its panic), and the
   bytes-two-ways panic (require_uncommitted's abort, then a panic). *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Msgs, Slots, Members, Pieces

S == 1..Slots
M == 1..Msgs
G == 1..Msgs   \* every group has a member, so at most one a message

Open == {"OpenEmpty", "OpenShort", "OpenShortDispatched", "OpenRooms"}
Wait == {"WaitSingle", "WaitRoomMulti", "WaitMulti", "WaitBatch", "WaitAborted"}

VARIABLES slot,                    \* each slot: its kind, message and group (0: none)
          free, endq, events,       \* free_slots, end_queue (slots), events (records)
          ended, taken,             \* the events owed, in end order; those next_event gave
          opened,                   \* messages opened
          grp, openG, nextG,        \* the groups, the open one (0: none), the next made
          mgroup, mwork, pieces, made, credit,  \* each message's group, tasks, room pieces, credits
          cpc                       \* the caller's place

vars == <<slot, free, endq, events, ended, taken, opened, grp, openG, nextG, mgroup, mwork, pieces, made, credit, cpc>>
work == <<grp, openG, nextG, mgroup, mwork, pieces, made, credit>>

FreeSlot == [kind |-> "Free", msg |-> 0, group |-> 0]
NoGroup == [st |-> "none", kind |-> "none", n |-> 0, credits |-> {}]

Init == /\ slot = [s \in S |-> FreeSlot]
        /\ free = [i \in 1..Slots |-> i] /\ endq = <<>> /\ events = <<>>
        /\ ended = <<>> /\ taken = <<>> /\ opened = 0
        /\ grp = [g \in G |-> NoGroup] /\ openG = 0 /\ nextG = 1
        /\ mgroup = [m \in M |-> 0] /\ mwork = [m \in M |-> "none"]
        /\ pieces = [m \in M |-> 0] /\ made = [m \in M |-> 0] /\ credit = [m \in M |-> 0]
        /\ cpc = "idle"

OpenCount == Cardinality({s \in S : slot[s].kind \in Open})
GroupDone(g) == IF g = 0 THEN TRUE ELSE grp[g].st = "done"

(* try_reap_one's test of slot s, holding message m. *)
Done(s) == LET x == slot[s]  m == x.msg IN
           CASE x.kind = "WaitSingle" -> GroupDone(x.group)
             [] x.kind = "WaitMulti" -> mwork[m] = "done"
             [] x.kind = "WaitBatch" -> IF x.group # 0 THEN GroupDone(x.group) ELSE mwork[m] = "done"
             [] x.kind = "WaitRoomMulti" -> pieces[m] = 0
             [] x.kind = "WaitAborted" -> pieces[m] = 0 /\ GroupDone(x.group)
FrontDone == endq # <<>> /\ Done(Head(endq))
Event(s) == [m |-> slot[s].msg,
             k |-> CASE slot[s].kind = "WaitAborted" -> "Aborted" [] slot[s].kind = "WaitBatch" -> "Batch" [] OTHER -> "Hashed"]

(* reap, as far as `cap` events: the end queue's done front, in order. *)
RECURSIVE Run(_, _)
Run(i, cap) == IF i > Len(endq) \/ i > cap \/ ~Done(endq[i]) THEN i - 1 ELSE Run(i + 1, cap)
ReapAt(cap) == LET n == Run(1, cap)
                   gone == {endq[i] : i \in 1..n}
               IN /\ events' = events \o [i \in 1..n |-> Event(endq[i])]
                  /\ free' = free \o SubSeq(endq, 1, n)
                  /\ endq' = SubSeq(endq, n + 1, Len(endq))
                  /\ slot' = [s \in S |-> IF s \in gone THEN FreeSlot ELSE slot[s]]
Reap == ReapAt(Slots - Len(events))

(* The groups, as one record: push_member and publish_open. *)
Groups == [grp |-> grp, open |-> openG, next |-> nextG]
Pub(R) == IF R.open = 0 THEN R ELSE [R EXCEPT !.grp[R.open].st = "published", !.open = 0]
\* A member of kind k (short messages, or small batches) for message m,
\* holding its Room's credit if c; a group of another kind is published first.
First(R, k) == IF R.open # 0 /\ R.grp[R.open].kind # k THEN Pub(R) ELSE R
Into(R, k) == LET R1 == First(R, k) IN IF R1.open # 0 THEN R1.open ELSE R1.next
Push(R, m, k, c, early) ==
    LET R1 == First(R, k)
        g == Into(R, k)
        grp1 == IF R1.open # 0 THEN R1.grp ELSE [R1.grp EXCEPT ![g] = [st |-> "open", kind |-> k, n |-> 0, credits |-> {}]]
        grp2 == [grp1 EXCEPT ![g].n = @ + 1, ![g].credits = IF c THEN @ \cup {m} ELSE @]
        R2 == [grp |-> grp2, open |-> g, next |-> IF R1.open # 0 THEN R1.next ELSE R1.next + 1]
    IN IF early \/ grp2[g].n = Members THEN Pub(R2) ELSE R2
SetGroups(R) == grp' = R.grp /\ openG' = R.open /\ nextG' = R.next
FrontInOpen == /\ openG # 0 /\ endq # <<>>
               /\ slot[Head(endq)].kind \in {"WaitSingle", "WaitBatch", "WaitAborted"}
               /\ slot[Head(endq)].group = openG
PublishIfFront == IF FrontInOpen THEN SetGroups(Pub(Groups)) ELSE UNCHANGED <<grp, openG, nextG>>

(* The caller. *)
\* message(): take a free slot, else reap and take one, else panic or wait.
Take == LET s == Head(free) IN
        /\ slot' = [slot EXCEPT ![s] = [kind |-> "OpenEmpty", msg |-> opened + 1, group |-> 0]]
        /\ free' = Tail(free) /\ opened' = opened + 1 /\ cpc' = "idle"
        /\ UNCHANGED <<endq, events, ended, taken, work>>
Message1 == /\ cpc \in {"idle", "message"} /\ opened < Msgs
            /\ IF free # <<>> THEN Take
               ELSE Reap /\ cpc' = "message2" /\ UNCHANGED <<ended, taken, opened, work>>
Message2 == /\ cpc = "message2"
            /\ IF free # <<>> THEN Take
               ELSE IF Len(events) >= Slots \/ OpenCount >= Slots
               THEN cpc' = "panicked" /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, work>>
               ELSE /\ PublishIfFront /\ cpc' = "messagewait"
                    /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, mgroup, mwork, pieces, made, credit>>
MessageWake == /\ cpc = "messagewait" /\ FrontDone /\ cpc' = "message"
               /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, work>>

\* ready(): reap; return with an event, else panic with nothing ended in
\* flight, else publish the front's open group and wait. The caller awaits it
\* where next_event gave none.
Ready1 == /\ \/ cpc = "idle" /\ events = <<>>
             \/ cpc = "ready"
          /\ Reap /\ cpc' = "ready2"
          /\ UNCHANGED <<ended, taken, opened, work>>
Ready2 == /\ cpc = "ready2"
          /\ IF events # <<>> THEN cpc' = "idle" /\ UNCHANGED <<grp, openG, nextG>>
             ELSE IF endq = <<>> THEN cpc' = "panicked" /\ UNCHANGED <<grp, openG, nextG>>
             ELSE PublishIfFront /\ cpc' = "readywait"
          /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, mgroup, mwork, pieces, made, credit>>
ReadyWake == /\ cpc = "readywait" /\ FrontDone /\ cpc' = "ready"
             /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, work>>

\* next_event(): the first waiting event, else reap one.
NextEvent == /\ cpc = "idle"
             /\ IF events # <<>>
                THEN /\ taken' = Append(taken, Head(events)) /\ events' = Tail(events)
                     /\ UNCHANGED <<slot, free, endq>>
                ELSE LET s == Head(endq) IN
                     /\ endq # <<>> /\ Done(s) /\ taken' = Append(taken, Event(s))
                     /\ endq' = Tail(endq) /\ free' = Append(free, s) /\ slot' = [slot EXCEPT ![s] = FreeSlot]
                     /\ UNCHANGED events
             /\ UNCHANGED <<ended, opened, work, cpc>>

\* A step on an open message's slot s: its kind, group and the end queue.
Hand(s, kind, g, k) == /\ slot' = [slot EXCEPT ![s].kind = kind, ![s].group = g]
                       /\ endq' = Append(endq, s) /\ ended' = Append(ended, [m |-> slot[s].msg, k |-> k])
Keep(s, kind, g) == slot' = [slot EXCEPT ![s].kind = kind, ![s].group = g] /\ UNCHANGED <<endq, ended>>
Piece(m) == /\ pieces' = [pieces EXCEPT ![m] = @ + 1] /\ made' = [made EXCEPT ![m] = @ + 1]
            /\ credit' = [credit EXCEPT ![m] = @ + 1]

CommitShort(s) == LET m == slot[s].msg IN
    /\ slot[s].kind = "OpenEmpty"
    /\ Keep(s, "OpenShort", 0) /\ credit' = [credit EXCEPT ![m] = @ + 1]
    /\ UNCHANGED <<grp, openG, nextG, mgroup, mwork, pieces, made>>
CommitRoom(s) == LET m == slot[s].msg IN
    /\ slot[s].kind \in {"OpenEmpty", "OpenRooms"} /\ made[m] < Pieces
    /\ Keep(s, "OpenRooms", 0) /\ Piece(m)
    /\ UNCHANGED <<grp, openG, nextG, mgroup, mwork>>
\* end, and end_slow.
End(s) == LET x == slot[s]  m == x.msg IN
    \/ /\ x.kind = "OpenEmpty" /\ Hand(s, "WaitSingle", 0, "Hashed") /\ UNCHANGED work
    \/ /\ x.kind = "OpenShort"
       /\ \E early \in BOOLEAN :
            /\ SetGroups(Push(Groups, m, "short", TRUE, early)) /\ mgroup' = [mgroup EXCEPT ![m] = Into(Groups, "short")]
            /\ Hand(s, "WaitSingle", Into(Groups, "short"), "Hashed")
       /\ UNCHANGED <<mwork, pieces, made, credit>>
    \/ /\ x.kind = "OpenShortDispatched" /\ Hand(s, "WaitSingle", x.group, "Hashed") /\ UNCHANGED work
    \/ /\ x.kind = "OpenRooms" /\ Hand(s, "WaitRoomMulti", 0, "Hashed") /\ UNCHANGED work
\* abort and abort_slot: a short Room's credit is given back here; a
\* dispatched one's group, and room pieces, give theirs back.
Abort(s) == LET x == slot[s]  m == x.msg IN
    /\ x.kind \in Open
    /\ Hand(s, "WaitAborted", IF x.kind = "OpenShortDispatched" THEN x.group ELSE 0, "Aborted")
    /\ credit' = IF x.kind = "OpenShort" THEN [credit EXCEPT ![m] = @ - 1] ELSE credit
    /\ UNCHANGED <<grp, openG, nextG, mgroup, mwork, pieces, made>>
\* owned and lent (submit_slice): a short slice is a group member, a long
\* one the slot's tasks.
SliceE(s, long, early) == LET m == slot[s].msg IN
    /\ slot[s].kind = "OpenEmpty"
    /\ IF long THEN Hand(s, "WaitMulti", 0, "Hashed") /\ mwork' = [mwork EXCEPT ![m] = "run"] /\ UNCHANGED <<grp, openG, nextG, mgroup>>
       ELSE /\ SetGroups(Push(Groups, m, "short", FALSE, early)) /\ mgroup' = [mgroup EXCEPT ![m] = Into(Groups, "short")]
            /\ Hand(s, "WaitSingle", Into(Groups, "short"), "Hashed") /\ UNCHANGED mwork
    /\ UNCHANGED <<pieces, made, credit>>
Slice(s) == \E long, early \in BOOLEAN : SliceE(s, long, early)
\* batch: of no messages (done at once), small (a group member), or large.
Batch(s) == LET m == slot[s].msg IN
    /\ slot[s].kind = "OpenEmpty"
    /\ \/ Hand(s, "WaitBatch", 0, "Batch") /\ mwork' = [mwork EXCEPT ![m] = "done"] /\ UNCHANGED <<grp, openG, nextG, mgroup>>
       \/ \E early \in BOOLEAN :
            /\ SetGroups(Push(Groups, m, "batch", FALSE, early)) /\ mgroup' = [mgroup EXCEPT ![m] = Into(Groups, "batch")]
            /\ Hand(s, "WaitBatch", Into(Groups, "batch"), "Batch") /\ UNCHANGED mwork
       \/ Hand(s, "WaitBatch", 0, "Batch") /\ mwork' = [mwork EXCEPT ![m] = "run"] /\ UNCHANGED <<grp, openG, nextG, mgroup>>
    /\ UNCHANGED <<pieces, made, credit>>
\* A wait for a Room (poll_room) sends each short Room on into a group
\* (flush_sealed_short_rooms), one a step, then publishes the open group.
FlushOne(s) == LET m == slot[s].msg IN
    /\ cpc \in {"idle", "flush"} /\ slot[s].kind = "OpenShort"
    /\ \E early \in BOOLEAN :
         /\ SetGroups(Push(Groups, m, "short", TRUE, early)) /\ mgroup' = [mgroup EXCEPT ![m] = Into(Groups, "short")]
         /\ Keep(s, "OpenShortDispatched", Into(Groups, "short"))
    /\ cpc' = "flush"
    /\ UNCHANGED <<free, events, taken, opened, mwork, pieces, made, credit>>
FlushEnd == /\ cpc = "flush" /\ \A s \in S : slot[s].kind # "OpenShort"
            /\ SetGroups(Pub(Groups)) /\ cpc' = "idle"
            /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, mgroup, mwork, pieces, made, credit>>

OnSlot(s) == /\ cpc = "idle"
             /\ (CommitShort(s) \/ CommitRoom(s) \/ End(s) \/ Abort(s) \/ Slice(s) \/ Batch(s))
             /\ UNCHANGED <<free, events, taken, opened, cpc>>

Finish == /\ cpc = "idle" /\ opened = Msgs /\ OpenCount = 0 /\ endq = <<>> /\ events = <<>>
          /\ cpc' = "finished" /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, work>>

Caller == Message1 \/ Message2 \/ MessageWake \/ Ready1 \/ Ready2 \/ ReadyWake \/ NextEvent
          \/ (\E s \in S : OnSlot(s) \/ FlushOne(s)) \/ FlushEnd \/ Finish

(* The workers. A group's run hashes its members and gives back the
   credits of their Rooms, then marks it complete; a slot's tasks set
   slot_done; a room piece gives back its Room's credit and is done. *)
RunGroup(g) == /\ grp[g].st = "published"
               /\ grp' = [grp EXCEPT ![g].st = "done"]
               /\ credit' = [m \in M |-> IF m \in grp[g].credits THEN credit[m] - 1 ELSE credit[m]]
               /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, openG, nextG, mgroup, mwork, pieces, made, cpc>>
RunTasks(m) == /\ mwork[m] = "run" /\ mwork' = [mwork EXCEPT ![m] = "done"]
               /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, grp, openG, nextG, mgroup, pieces, made, credit, cpc>>
RunPiece(m) == /\ pieces[m] > 0
               /\ pieces' = [pieces EXCEPT ![m] = @ - 1] /\ credit' = [credit EXCEPT ![m] = @ - 1]
               /\ UNCHANGED <<slot, free, endq, events, ended, taken, opened, grp, openG, nextG, mgroup, mwork, made, cpc>>
Worker == (\E g \in G : RunGroup(g)) \/ \E m \in M : RunTasks(m) \/ RunPiece(m)

Next == Caller \/ Worker
Spec == Init /\ [][Next]_vars /\ WF_vars(Caller)
        /\ \A g \in G : WF_vars(RunGroup(g)) /\ \A m \in M : WF_vars(RunTasks(m)) /\ WF_vars(RunPiece(m))

(* Safety. *)
Msg(s) == slot[s].msg
\* Events come out in end order, each once: next_event's, then those waiting,
\* then the end queue's slots, are the ended messages in the order ended.
InEndOrder == /\ Len(taken) + Len(events) + Len(endq) = Len(ended)
              /\ \A i \in 1..Len(taken) : taken[i] = ended[i]
              /\ \A i \in 1..Len(events) : events[i] = ended[Len(taken) + i]
              /\ \A i \in 1..Len(endq) : Msg(endq[i]) = ended[Len(taken) + Len(events) + i].m
\* Every slot is free, open, or ended in the end queue: reap frees a slot as
\* it moves the slot's event out, so a waiting event holds no slot.
SlotsAccounted == /\ Len(free) + Len(endq) + OpenCount = Slots
                  /\ \A i \in 1..Len(free) : slot[free[i]].kind = "Free"
                  /\ \A i \in 1..Len(endq) : slot[endq[i]].kind \in Wait
                  /\ Cardinality({free[i] : i \in 1..Len(free)} \cup {endq[i] : i \in 1..Len(endq)}) = Len(free) + Len(endq)
\* A message's event comes once its work is done: no room piece, group or
\* task of it is left, and its Rooms' credits are all given back (an
\* aborted one's too).
Reaped == {events[i].m : i \in 1..Len(events)} \cup {taken[i].m : i \in 1..Len(taken)}
EventsAfterWork == \A m \in Reaped : /\ pieces[m] = 0 /\ credit[m] = 0 /\ GroupDone(mgroup[m]) /\ mwork[m] # "run"
CreditsNonNegative == \A m \in M : credit[m] >= 0
\* At most `Slots` events wait (reap's bound).
EventsBounded == Len(events) <= Slots
\* A caller that finishes took every message's event.
FinishedTookAll == cpc = "finished" => Len(taken) = Msgs

\* Each slot moves only as the code moves it.
Edges == {<<"Free", "OpenEmpty">>}
         \cup {<<"OpenEmpty", k>> : k \in {"OpenShort", "OpenRooms", "WaitSingle", "WaitAborted", "WaitMulti", "WaitBatch"}}
         \cup {<<"OpenShort", k>> : k \in {"OpenShortDispatched", "WaitSingle", "WaitAborted"}}
         \cup {<<"OpenShortDispatched", k>> : k \in {"WaitSingle", "WaitAborted"}}
         \cup {<<"OpenRooms", k>> : k \in {"WaitRoomMulti", "WaitAborted"}}
         \cup {<<k, "Free">> : k \in Wait}
SlotsMove == [][\A s \in S : slot'[s].kind = slot[s].kind \/ <<slot[s].kind, slot'[s].kind>> \in Edges]_vars

(* Liveness: the caller's waits all end, so it opens every message and takes
   every event, unless it called a wait the code refuses (the panics). *)
Finishes == <>(cpc \in {"finished", "panicked"})
=============================================================================
