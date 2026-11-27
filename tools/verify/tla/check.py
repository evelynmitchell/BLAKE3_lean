#!/usr/bin/env python3
"""Check the TLA+ models of the pool's handshakes, and that each fails for its planted faults.

    python3 tools/verify/tla/check.py              # every model, then every control
    python3 tools/verify/tla/check.py --models     # the models alone

The models (Finish.tla, Waker.tla, Park.tla) state threads/src/finish.rs,
waker.rs and park.rs one atomic operation an action, and PipeRooms.tla,
PipeTasks.tla and PipeStorage.tla the Pipeline's (pipeline.rs) rooms and
their credits, messages hashed in parts, loans and groups, a storage
outliving its Pipeline, PipeSlots.tla its message slots and the order of
their events, PipeQueue.tla its source's action queue and its rings, and
PipeShort.tla short messages sharing Rooms and groups, and batches, and
Turn.tla the workers' choice among sources
(lanes.rs, run_one), and TLC checks every
schedule of a small instance: the safety properties as invariants, and that
no wake is lost as a liveness property under weak fairness, which Shuttle's
sampled schedules cannot state. They model the code; they are not it. The
names of the actions follow the functions they model, for a reader to
compare.

Then the models are checked against the code (trace validation): the
Shuttle tests of finish.rs, waker.rs (both) and park.rs
(owed_wakes_cascade) log every schedule, operation by operation, and each
log, turned into its model's actions, must be a behavior of the model
(FinishTrace.tla, WakerTrace.tla, ParkTrace.tla).

A model that passes proves nothing until it is seen to fail: each control
plants one fault (a re-check left out, a count read apart from its bit, a
wake not passed on) in a copy of the models, in a temporary directory, and
TLC must find a violation. The models here are never edited.

TLC is tla2tools.jar 1.7.4, pinned by SHA-256 and BLAKE3 (checked with
tools/blake3_ref.py), downloaded once into tmp/tla/ (or named by $TLA2TOOLS);
it needs Java 11 or later.
"""

import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import blake3_ref  # noqa: E402

JAR_URL = "https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar"
JAR_SHA256 = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
JAR_BLAKE3 = "36e4d95a99aa33dde9ff7b288bf3092f3dfbb26e450fc9758ee765cdb250ce38"

# (model, its .cfg): each model module and its configuration.
MODELS = ["Finish", "MCWaker", "MCWakerSwap", "MCPark", "MCParkLeave", "PipeRooms", "PipeTasks", "PipeStorage", "PipeSlots", "MCPipeSlotsOne", "PipeQueue", "MCPipeQueueFull", "PipeShort", "Turn"]

# (model, what the fault is, file, text to find once, its replacement, ...more
# pairs of text and replacement for a fault that moves a step). The
# Pipeline's ten are tools/pipeline_model_controls.py's, in the models.
CONTROLS = [
    ("Finish", "the finisher compares the count before its own piece (never unparks)", "Finish.tla",
     "IF sleeping /\\ count + 1 = Target THEN", "IF sleeping /\\ count = Target THEN"),
    ("Finish", "the caller parks on the count it polled, not the one read with its bit", "Finish.tla",
     "             /\\ sleeping' = TRUE /\\ have' = count            \\* one fetch_or\n             /\\ wpc' = IF count < Target THEN \"park\" ELSE \"clear\"",
     "             /\\ sleeping' = TRUE /\\ have' = have\n             /\\ wpc' = IF have < Target THEN \"park\" ELSE \"clear\""),
    ("Finish", "the caller returns on any wake, without re-reading the count", "Finish.tla",
     "SpuriousWake == /\\ wpc = \"park\" /\\ wpc' = \"recheck\"", "SpuriousWake == /\\ wpc = \"park\" /\\ wpc' = \"clear\""),
    ("MCWaker", "the caller does not re-check after registering", "Waker.tla",
     "             /\\ cpc' = IF done > seen THEN \"clear0\" ELSE \"pending\"", "             /\\ cpc' = \"pending\""),
    ("MCWaker", "the worker takes the Waker while the caller writes it", "Waker.tla",
     "              /\\ IF state = \"registered\"\n                 THEN state' = \"waking\"",
     "              /\\ IF state \\in {\"registered\", \"writing\"}\n                 THEN state' = \"waking\""),
    ("MCPark", "the worker parks without looking again after setting its bit", "Park.tla",
     "              /\\ wpc' = [wpc EXCEPT ![w] = IF work > 0 \\/ AllDone THEN \"clearown\" ELSE \"park\"]",
     "              /\\ wpc' = [wpc EXCEPT ![w] = \"park\"]"),
    ("MCParkLeave", "a worker leaving with work drops a wake meant for it (not passed on)", "Park.tla",
     "IF parked[w] THEN \"look\" ELSE \"passon\"", "\"look\""),
    ("PipeTasks", "Pipeline 1: a group is published done before its members are hashed", "PipeTasks.tla",
     "/\\ gpc = \"run\" /\\ groupDone = FALSE", "/\\ gpc = \"complete\" /\\ groupDone = FALSE",
     "/\\ groupDone' = TRUE /\\ gpc' = \"end\"", "/\\ groupDone' = TRUE /\\ gpc' = \"run\"",
     "/\\ members' = [m \\in 1..Members |-> TRUE] /\\ gpc' = \"complete\"", "/\\ members' = [m \\in 1..Members |-> TRUE] /\\ gpc' = \"end\""),
    ("PipeRooms", "Pipeline 2: a finished task wakes no one", "PipeRooms.tla",
     "![p].done = TRUE]\n              /\\ Notify", "![p].done = TRUE]\n              /\\ UNCHANGED <<registered, woken>>"),
    ("PipeRooms", "Pipeline 3: a room piece is published done before it is hashed", "PipeRooms.tla",
     "/\\ piece' = [piece EXCEPT ![p].pc = \"reading\"]", "/\\ piece' = [piece EXCEPT ![p].pc = \"reading\", ![p].done = TRUE]"),
    ("PipeRooms", "Pipeline 4: a room piece gives its room back before it has read it", "PipeRooms.tla",
     "/\\ piece' = [piece EXCEPT ![p].pc = \"reading\"]\n              /\\ UNCHANGED <<refs, gen,",
     "/\\ piece' = [piece EXCEPT ![p].pc = \"reading\"]\n              /\\ refs' = [refs EXCEPT ![piece[p].room] = refs[piece[p].room] - 1]\n              /\\ UNCHANGED <<gen,"),
    ("PipeTasks", "Pipeline 5 and 10: a message's (a batch's) parts are published done before the last is hashed", "PipeTasks.tla",
     "IF left = 1 THEN \"fold\" ELSE \"end\"", "IF left # 0 THEN \"fold\" ELSE \"end\""),
    ("PipeStorage", "Pipeline 6: a storage goes back on the free list while a Room still holds it", "PipeStorage.tla",
     "IF holders = n THEN", "IF holders >= n THEN"),
    ("PipeRooms", "Pipeline 7: a Room's drop gives back one credit more than it has", "PipeRooms.tla",
     "LET unused == Credits - commits[r]", "LET unused == Credits - commits[r] + (IF commits[r] # 0 THEN 1 ELSE 0)"),
    ("PipeRooms", "Pipeline 8: a Room's drop wakes no one", "PipeRooms.tla",
     "IF prev = unused THEN Notify ELSE UNCHANGED <<registered, woken>>", "UNCHANGED <<registered, woken>>"),
    ("PipeTasks", "Pipeline 9: a loan's event comes before the loan is marked complete", "PipeTasks.tla",
     "/\\ ppc' = [ppc EXCEPT ![p] = \"loan\"]", "/\\ ppc' = [ppc EXCEPT ![p] = \"publish\"]",
     "/\\ loanDone' = TRUE /\\ ppc' = [ppc EXCEPT ![p] = \"publish\"]", "/\\ loanDone' = TRUE /\\ ppc' = [ppc EXCEPT ![p] = \"end\"]",
     "/\\ slotDone' = TRUE /\\ ppc' = [ppc EXCEPT ![p] = \"end\"]", "/\\ slotDone' = TRUE /\\ ppc' = [ppc EXCEPT ![p] = \"loan\"]"),
    ("PipeSlots", "next_event takes any done slot's event, not the end queue's front's", "PipeSlots.tla",
     "ELSE LET s == Head(endq) IN\n                     /\\ endq # <<>> /\\ Done(s) /\\ taken' = Append(taken, Event(s))\n                     /\\ endq' = Tail(endq)",
     "ELSE \\E i \\in 1..Len(endq) : LET s == endq[i] IN\n                     /\\ endq # <<>> /\\ Done(s) /\\ taken' = Append(taken, Event(s))\n                     /\\ endq' = SubSeq(endq, 1, i - 1) \\o SubSeq(endq, i + 1, Len(endq))"),
    ("PipeSlots", "an aborted slot is freed before its group finishes (WaitAborted)", "PipeSlots.tla",
     '[] x.kind = "WaitAborted" -> pieces[m] = 0 /\\ GroupDone(x.group)', '[] x.kind = "WaitAborted" -> pieces[m] = 0'),
    ("PipeSlots", "a slot goes back on the free list when its message is ended, before its event", "PipeSlots.tla",
     "             /\\ UNCHANGED <<free, events, taken, opened, cpc>>",
     "             /\\ free' = IF slot'[s].kind \\in Wait THEN Append(free, s) ELSE free\n             /\\ UNCHANGED <<events, taken, opened, cpc>>"),
    ("PipeSlots", "ready() waits with nothing ended in flight (no refusal)", "PipeSlots.tla",
     "ELSE IF endq = <<>> THEN cpc' = \"panicked\"", "ELSE IF endq = <<>> THEN cpc' = \"readywait\""),
    ("MCPipeSlotsOne", "message() waits with every event untaken (no refusal)", "PipeSlots.tla",
     "IF Len(events) >= Slots \\/ OpenCount >= Slots", "IF OpenCount >= Slots"),
    ("PipeSlots", "a wait does not publish the open group the end queue's front is in", "PipeSlots.tla",
     "PublishIfFront == IF FrontInOpen THEN", "PublishIfFront == IF FALSE THEN"),
    ("PipeQueue", "a taker claims its action without comparing claimed (taken twice)", "PipeQueue.tla",
     "Won(t) == claimed + 1 = take[t].n", "Won(t) == take[t].n # 0"),
    ("PipeQueue", "a wait sleeps without wake_for_waiting", "PipeQueue.tla",
     "/\\ IF Waiting > 0 THEN Wake ELSE UNCHANGED wpc        \\* wake_for_waiting", "/\\ UNCHANGED wpc"),
    ("MCPipeQueueFull", "the action ring is one short of what is handed out", "PipeQueue.tla",
     "ActionRing == Slots * MaxPieces + Nodes + Groups", "ActionRing == Slots * MaxPieces + Nodes + Groups - 1"),
    ("PipeQueue", "free_pieces is one short of the nodes", "PipeQueue.tla", "PieceRing == Nodes", "PieceRing == Nodes - 1"),
    ("PipeQueue", "free_slots is one short of the slots", "PipeQueue.tla", "SlotRing == Slots", "SlotRing == Slots - 1"),
    ("PipeQueue", "local_free_rooms is one short of the rooms", "PipeQueue.tla",
     "RoomRing == IF Rooms > 1 THEN Rooms ELSE 1", "RoomRing == Rooms - 1"),
    ("PipeShort", "a group is reused before its epoch completes", "PipeShort.tla",
     "         /\\ IF ~InFlight(g)\n            THEN JoinAt", "         /\\ IF TRUE\n            THEN JoinAt"),
    ("PipeShort", "Pipeline::drop gives back the credits of published groups' members too (released twice)", "PipeShort.tla",
     "(Short(m) /\\ openG # 0 /\\ m \\in InGroup(openG))", "(Short(m) /\\ msg[m].g # 0)"),
    ("PipeShort", "a group is filled without its members' rooms in its metas (credits never back)", "PipeShort.tla",
     "metas |-> Append(rs, msg[m].r)", "metas |-> Append(rs, 0)"),
    ("PipeShort", "a member's event (a batch's digests) is read before its group completes", "PipeShort.tla",
     "Ready(m) == IF msg[m].g = 0 THEN TRUE ELSE completed[msg[m].g] >= msg[m].e", "Ready(m) == TRUE"),
    ("Turn", "every walk starts at slot 0 (no turns: a streaming Pipeline starves the rest)", "Turn.tla",
     "      start == IF inTurn THEN cursor[w] ELSE 1", "      start == 1"),
    ("Turn", "a turn's cursor stays on the slot it served", "Turn.tla",
     "cursor' = [cursor EXCEPT ![w] = (s % Sources) + 1]", "cursor' = [cursor EXCEPT ![w] = s]"),
]


def jar():
    path = os.environ.get("TLA2TOOLS") or os.path.join(ROOT, "tmp", "tla", "tla2tools.jar")
    if not os.path.exists(path):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with urllib.request.urlopen(JAR_URL, timeout=300) as r, open(path + ".part", "wb") as f:
            shutil.copyfileobj(r, f)
        os.replace(path + ".part", path)
    data = open(path, "rb").read()
    sha, b3 = hashlib.sha256(data).hexdigest(), blake3_ref.blake3_hex(data)
    if (sha, b3) != (JAR_SHA256, JAR_BLAKE3):
        sys.exit(f"check.py: {path} is not the pinned tla2tools.jar (SHA-256 {sha}, BLAKE3 {b3})")
    return path


def tlc(tla_jar, directory, model, deadlock=False):
    """TLC on `model` in `directory`: (passed, its output's last lines).
    A deadlock is no error unless `deadlock` (the trace checks': a trace
    the model cannot take further is one)."""
    with tempfile.TemporaryDirectory() as meta:
        r = subprocess.run(["java", "-XX:+UseParallelGC", "-cp", tla_jar, "tlc2.TLC", "-workers", "auto"] + ([] if deadlock else ["-deadlock"]) +
                           ["-nowarning", "-metadir", meta, "-config", model + ".cfg", model],
                           cwd=directory, capture_output=True, text=True)
    out = r.stdout + r.stderr
    passed = r.returncode == 0 and "Model checking completed. No error has been found." in out
    return passed, out


# Trace validation (FinishTrace.tla): Shuttle's schedules of the real
# finish.rs, logged by tests/shuttle_finish.rs's primitives, each checked
# as a behavior of Finish.tla.
SLEEPING = 1 << 63
CALLER = "ThreadId { task_id: main-thread(0) }"


def record(tree, build, test, variable):
    """Run tests/`test`.rs in `tree` (a checkout), building in `build`,
    with `variable` naming the file its schedules' logs go to: each
    schedule's log, a line a schedule."""
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "trace")
        env = dict(os.environ, RUSTFLAGS="--cfg shuttle", CARGO_TARGET_DIR=build, **{variable: out})
        r = subprocess.run(["cargo", "test", "-q", "--release", "--test", test, "--", "--test-threads=1"],
                           cwd=os.path.join(tree, "threads"), env=env, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"check.py: tests/{test}.rs failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
        return open(out).read().splitlines()


def record_finish(tree, build):
    return record(tree, build, "shuttle_finish", "FINISH_TRACE")


def record_waker(tree, build):
    return record(tree, build, "shuttle_waker", "WAKER_TRACE")


# WakerScripts.tla's scripts, by the name tests/shuttle_waker.rs tags a line with.
SCRIPTS = {"OneWait": ["wait"], "Swap": ["register", "register", "clear"]}


def waker_trace(line):
    """One schedule of a tests/shuttle_waker.rs test, tagged with its
    caller's script (WakerScripts.tla), as Waker.tla's actions: (the
    script's name, the trace). The caller (the main thread) runs its
    script's steps: a wait's Check reads `done`, a register's and a clear's
    is the step's start; then register's fast path or loop, Recheck, the
    wait, clear. The worker (the thread that sets `done`) and the others
    notify (notify_after_seqcst, wake_slow). A wake_slow that took no Waker
    wakes nothing: its Wake3 follows its store at once."""
    name, line = line.split(":", 1)
    script = SCRIPTS[name]
    events = [e.split("|") for e in line.split(";")]
    workers = {t for (t, what, op, _) in events if what == "done" and op == "swap"}
    others = sorted({t for (t, _, _, _) in events if t != CALLER and t not in workers})
    number = {t: 0 for t in workers} | {t: k + 1 for k, t in enumerate(others)}
    out, phase, step = [], "top", 0
    act = lambda a: out.append(f'[a |-> "{a}"]')

    def stepped():
        nonlocal step, phase
        step += 1
        phase = "top" if step < len(script) else "end"

    def registered():   # a wait re-checks its item; a register is done
        nonlocal phase
        if script[step] == "wait":
            phase = "recheck"
        else:
            stepped()

    def cleared():   # a wait takes its item; a clear is done
        if script[step] == "wait":
            act("Got")
        stepped()

    for k, (thread, what, op, value) in enumerate(events):
        if thread == CALLER:
            if phase == "end":
                continue
            word = op.split()
            if phase == "top" and script[step] != "wait":
                act("Check"); phase = "fast" if script[step] == "register" else "clear"
            if phase == "top" and what == "done":
                act("Check")
                if value == "true":
                    act("Got"); stepped()
                else:
                    phase = "fast"
            elif phase == "fast" and word[0] == "cas":
                act("Fast"); phase = "compare" if word[1] == word[2] else "load"
            elif phase == "compare" and what == "cell":
                act("Compare"); phase = "fastback"
            elif phase == "fastback" and word[0] == "store":
                # will_wake: a wait's Waker is the one before; a register's is new.
                act("FastBack")
                if script[step] == "wait":
                    registered()
                else:
                    phase = "load"
            elif phase == "load" and word[0] == "load":
                act("Load"); phase = "cas" if word[1] in ("0", "2") else "load"
            elif phase == "cas" and word[0] == "cas":
                act("Cas"); phase = "put" if word[1] == word[2] else "load"
            elif phase == "put" and what == "cell":
                act("Put"); phase = "putback"
            elif phase == "putback" and word[0] == "store":
                act("PutBack"); registered()
            elif phase == "recheck" and what == "done":
                act("Recheck"); phase = "clear" if value == "true" else "pending"
            elif phase == "pending" and what == "woken":
                if value == "true":
                    act("Wake"); phase = "top"
            elif phase == "clear" and word[0] == "load":
                if word[1] == "0":
                    act("Clear0"); cleared()
                elif word[1] == "2":
                    phase = "clearcas"
                else:
                    act("Clear0")   # spinning while another holds the slot
            elif phase == "clearcas" and word[0] == "cas":
                if word[1] == word[2]:
                    act("Clear0"); phase = "clear1"
                else:
                    phase = "clear"
            elif phase == "clear1" and what == "cell":
                act("Clear1"); phase = "clear2"
            elif phase == "clear2" and word[0] == "store":
                act("Clear2"); cleared()
            else:
                sys.exit(f"check.py: the caller's {what} {op} {value} in phase {phase} is no Waker.tla action")
        else:
            n = number[thread]
            nact = lambda a: out.append(f'[a |-> "{a}", n |-> {n}]')
            word = op.split()
            if what == "done" and op == "swap":
                nact("Finish")
            elif what == "state" and word[0] == "load":
                nact("Notify")
            elif what == "state" and word[0] == "cas":
                nact("Wake0")
            elif what == "cell":
                nact("Wake1")
            elif what == "state" and word[0] == "store":
                nact("Wake2")
                after = next(((w, o) for (t, w, o, _) in events[k + 1:] if t == thread), None)
                if after != ("woken", "store"):
                    nact("Wake3")
            elif what == "woken" and op == "store":
                nact("Wake3")
            else:
                sys.exit(f"check.py: a notifier's {what} {op} is no Waker.tla action")
    return name, "<<" + ", ".join(out) + ">>"


def record_park(tree, build):
    return record(tree, build, "shuttle_park", "PARK_TRACE")


def task(thread):
    """A Shuttle thread's number (`main-thread(k)`)."""
    return int(thread.rsplit("(", 1)[1].split(")")[0])


def park_trace(line, fanout=1):
    """One schedule of tests/shuttle_park.rs's owed_wakes_cascade as
    Park.tla's actions: workers (tasks 1 to 3, bits 0 to 2) through
    park_unless and pay_owed; the publisher (task 4) through its store and
    wake_for. wake_one's loop is one step where it decides; a pay_owed that
    has made its `fanout` wakes ends with no load, where the model reads
    the owed word once more (a PayLoad that finds the fan-out spent)."""
    events = [e.split("|") for e in line.split(";")]
    out, phase, made, last_wake, owe_pending = [], {}, {}, None, False
    act = lambda a, **kw: out.append("[" + ", ".join([f'a |-> "{a}"'] + [f"{k} |-> {v}" for k, v in kw.items()]) + "]")

    def wake(thread, word, mask_or_bits, before_or_none):
        """A wake_one event: None while undecided, else the bit's worker (0: none)."""
        if word[0] == "load":
            return 0 if int(word[1]) == 0 else None
        before, mask = int(word[1]), int(word[2])
        bit = ~mask & ((1 << 64) - 1)
        if before & bit:
            return bit.bit_length()
        return 0 if before & ~bit == 0 else None

    for k, (thread, what, op) in enumerate(events):
        n, word = task(thread), op.split()
        if n == 4:
            if what == "published":
                act("Publish")
            elif what == "word0" and not phase.get(4):
                act("WakeFor"); phase[4] = "owe"
                after = next(((w, o) for (t, w, o) in events[k + 1:] if task(t) == 4), None)
                if not after or after[0] != "word1":
                    act("WakeOwed"); phase[4] = "wake"
            elif what == "word1":
                if word[0] == "cas" and word[1] == word[2]:
                    act("WakeOwed"); phase[4] = "wake"
            elif what == "word0":
                u = wake(thread, word, None, None)
                if u is not None:
                    act("WakeNow", u=u); last_wake = u
            else:
                sys.exit(f"check.py: the publisher's {what} {op} is no Park.tla action")
            continue
        w, p = n, phase.get(n, "setbit")
        if p == "setbit" and what == "word0" and word[0] == "or":
            act("SetBit", w=w); p = "visible"
        elif p == "visible" and what == "published":
            act("Visible", w=w); p = "clearown" if int(word[1]) > 0 else "park"
        elif p == "clearown" and what == "word0" and word[0] == "and":
            act("ClearOwn", w=w)
            p = "end" if int(word[1]) & (1 << (w - 1)) else "passon"
        elif p == "passon" and what == "word0":
            u = wake(thread, word, None, None)
            if u is not None:
                act("PassOn", w=w, u=u); p = "pay"; made[w] = 0
        elif p == "park" and what == "word0" and word[0] == "load":
            act("ParkLoad", w=w)
            if int(word[1]) & (1 << (w - 1)) == 0:
                p = "pay"; made[w] = 0
        elif p == "park" and what == "park":
            act("ParkRet", w=w)
        elif p == "pay" and what == "word1" and word[0] == "load":
            act("PayLoad", w=w)
            p = "paycas" if int(word[1]) & 0xFFFFFFFF and made[w] < fanout else "end"
        elif p == "paycas" and what == "word1" and word[0] == "cas":
            act("PayCas", w=w); p = "paywake" if word[1] == word[2] else "pay"
        elif p == "paywake" and what == "word0":
            u = wake(thread, word, None, None)
            if u is not None:
                act("PayWake", w=w, u=u)
                if u == 0:
                    p = "payclear"
                else:
                    made[w] += 1
                    if made[w] >= fanout:
                        act("PayLoad", w=w); p = "end"
                    else:
                        p = "pay"
        elif p == "payclear" and what == "word1" and word[0] == "cas":
            act("PayClear", w=w); p = "end"
        else:
            sys.exit(f"check.py: worker {w}'s {what} {op} in phase {p} is no Park.tla action")
        phase[n] = p
    if last_wake != 0:
        act("WakeEnd")
    return "<<" + ", ".join(out) + ">>"


def check_park_traces(tla_jar, models, lines):
    """Every distinct schedule in `lines` against Park.tla (three workers,
    one wake a hop, one batch of three)."""
    ts = {park_trace(line) for line in lines}
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(models):
            if f.endswith(".tla"):
                shutil.copy(os.path.join(models, f), d)
        with open(os.path.join(d, "ParkTraceBatches.tla"), "w") as f:
            f.write("---- MODULE ParkTraceBatches ----\nOne == <<3>>\n====\n")
        return check_traces(tla_jar, d, "ParkTrace", {"Workers = 3\n          Fanout = 1\n          Batches <- One\n          Leave = FALSE": (ts, len(lines))},
                            extends="ParkTraceBatches")


def check_waker_traces(tla_jar, models, lines):
    """Every distinct schedule in `lines` against Waker.tla, with its test's
    script and one other notifier."""
    groups = {}
    for line in lines:
        name, trace = waker_trace(line)
        ts, n = groups.get(f"Script <- {name}\n          Others = 1", (set(), 0))
        groups[f"Script <- {name}\n          Others = 1"] = (ts | {trace}, n + 1)
    return check_traces(tla_jar, models, "WakerTrace", groups, extends="WakerScripts")


def finish_trace(pieces, line):
    """One schedule's log as Finish.tla's actions, a TLA+ sequence. The
    caller is the test's main thread: its loads of the count before it
    sets its bit are polls, after it re-checks; past its return (a poll
    that finds the count whole, or Clear) it is the test's. A finisher's
    load of `published` is part of its Add."""
    events = [e.rsplit(" ", 3) for e in line.split(";")]
    out, done, slept, finishers = [], False, False, {}
    for k, (thread, op, atomic, value) in enumerate(events):
        if op == "store":
            continue
        if thread == CALLER:
            if done:
                continue
            if op == "load" and atomic == "1" and not slept:
                if int(value) & ~SLEEPING >= pieces:
                    to, done = "done", True
                else:
                    after = next((o for (t, o, _, _) in events[k + 1:] if t == CALLER), None)
                    to = "setbit" if after == "fetch_or" else "poll"
                out.append(f'[a |-> "Poll", to |-> "{to}"]')
            elif op == "fetch_or":
                out.append('[a |-> "SetBit"]')
                slept = True
            elif op == "park":
                out.append('[a |-> "Park"]')
            elif op == "load" and atomic == "1":
                out.append('[a |-> "Recheck"]')
            elif op == "fetch_and":
                out.append('[a |-> "Clear"]')
                done = True
            else:
                sys.exit(f"check.py: the caller's {op} of atomic {atomic} is no Finish.tla action")
        else:
            f = finishers.setdefault(thread, len(finishers) + 1)
            if op == "fetch_add":
                out.append(f'[a |-> "Add", f |-> {f}]')
            elif op == "unpark":
                out.append(f'[a |-> "Unpark", f |-> {f}]')
            elif not (op == "load" and atomic == "0"):
                sys.exit(f"check.py: a finisher's {op} of atomic {atomic} is no Finish.tla action")
    return "<<" + ", ".join(out) + ">>"


def check_traces(tla_jar, models, spec, groups, extends=None):
    """Every distinct trace against `spec` (FinishTrace, WakerTrace), with
    `models` a directory of the .tla files. `groups` maps a configuration
    (the CONSTANTS lines, a string) to (the traces' TLA+ sequences, how many
    schedules gave them). (passed, what TLC said)."""
    said = []
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(models):
            if f.endswith(".tla"):
                shutil.copy(os.path.join(models, f), d)
        for k, (constants, (ts, schedules)) in enumerate(sorted(groups.items())):
            name = f"MC{spec}{k}"
            with open(os.path.join(d, name + ".tla"), "w") as f:
                f.write(f"---- MODULE {name} ----\nEXTENDS {spec}{', ' + extends if extends else ''}\nMCTraces == <<\n" + ",\n".join(sorted(ts)) + "\n>>\n====\n")
            with open(os.path.join(d, name + ".cfg"), "w") as f:
                f.write(f"SPECIFICATION TSpec\nCONSTANTS {constants}\n          Traces <- MCTraces\nINVARIANT Ends\n")
            passed, out = tlc(tla_jar, d, name, deadlock=True)
            found = next((line for line in out.splitlines() if "Deadlock" in line or "violated" in line), "")
            label = " ".join(constants.split())
            said.append(f"{label}: {len(ts)} distinct of {schedules} schedules{', ' + found if found else ''}")
            if not passed:
                return False, "; ".join(said) + "\n" + out[-2500:]
    return True, "; ".join(said)


def check_finish_traces(tla_jar, models, lines):
    """Every distinct schedule in `lines` against Finish.tla."""
    groups = {}
    for line in lines:
        pieces, log = line.split("|", 1)
        ts, n = groups.get(f"Finishers = {pieces}\n          Target = {pieces}", (set(), 0))
        ts.add(finish_trace(int(pieces), log))
        groups[f"Finishers = {pieces}\n          Target = {pieces}"] = (ts, n + 1)
    return check_traces(tla_jar, models, "FinishTrace", groups)


def model_control(tla_jar, file, old, new, check, lines):
    """The trace check of `lines` with `old` made `new` in a copy of the
    models' `file`: (passed, what TLC said)."""
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(HERE):
            if f.endswith(".tla"):
                shutil.copy(os.path.join(HERE, f), d)
        path = os.path.join(d, file)
        text = open(path).read()
        if text.count(old) != 1:
            sys.exit(f"check.py: the control's text is not in {file} once: {old!r}")
        open(path, "w").write(text.replace(old, new))
        return check(tla_jar, d, lines)


def code_control(tla_jar, source, old, new, recorder, check):
    """The trace check of the schedules recorded from a copy of the tree
    (in the build directory, never the tree) with `old` made `new` in
    `source`: (passed, what TLC said)."""
    import pipeline_model_controls
    build = os.path.join(os.path.abspath(os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")), "trace-controls")
    tree = os.path.join(build, "tree")
    pipeline_model_controls.make_copy(tree)
    path = os.path.join(tree, source)
    text = open(path).read()
    if text.count(old) != 1:
        sys.exit(f"check.py: the control's text is not in {source} once: {old!r}")
    open(path, "w").write(text.replace(old, new))
    return check(tla_jar, HERE, recorder(tree, os.path.join(build, "target")))


def trace_controls(tla_jar, finish_lines, waker_lines, park_lines):
    """The trace checks fail for a model narrowed past the code, and for
    code the model does not follow: (what, passed, what TLC said)."""
    return [
        ("Finish.tla's Add allowed only with the bit clear (narrower than the code)",
         *model_control(tla_jar, "Finish.tla", 'Add(f) ==    /\\ fpc[f] = "add"', 'Add(f) ==    /\\ fpc[f] = "add" /\\ ~sleeping',
                        check_finish_traces, finish_lines)),
        ("finish.rs's finished() unparks with no sleeper (the model does not)",
         *code_control(tla_jar, "threads/src/finish.rs",
                       "if before & SLEEPING != 0 && (before & !SLEEPING) + n == self.published.load(Ordering::SeqCst) {",
                       "if (before & !SLEEPING) + n == self.published.load(Ordering::SeqCst) {", record_finish, check_finish_traces)),
        ("Waker.tla's notifiers notify only once the item is done (narrower than the code)",
         *model_control(tla_jar, "Waker.tla", 'Notify(n) ==  /\\ npc[n] = "notify"', 'Notify(n) ==  /\\ npc[n] = "notify" /\\ done > 0',
                        check_waker_traces, waker_lines)),
        ("Waker.tla's register has no fast path (narrower than the code: the second test takes it)",
         *model_control(tla_jar, "Waker.tla", 'Fast ==       /\\ cpc = "fast"\n              /\\ IF state = "registered"',
                        'Fast ==       /\\ cpc = "fast"\n              /\\ IF FALSE', check_waker_traces, waker_lines)),
        ("waker.rs's notify_after_seqcst() tries wake_slow whenever the slot is not IDLE (the model does not)",
         *code_control(tla_jar, "threads/src/waker.rs", "if self.state.0.load(Ordering::SeqCst) == REGISTERED {",
                       "if self.state.0.load(Ordering::SeqCst) != IDLE {", record_waker, check_waker_traces)),
        ("Park.tla's payer reads the owed word only while something is owed (narrower than the code)",
         *model_control(tla_jar, "Park.tla", 'PayLoad(w) == /\\ wpc[w] = "payload"', 'PayLoad(w) == /\\ wpc[w] = "payload" /\\ owedCount > 0',
                        check_park_traces, park_lines)),
        ("park.rs's wake_for asks for one wake more than it needs (the model does not)",
         *code_control(tla_jar, "threads/src/park.rs", "let (now, later) = split(wanted.saturating_sub(workers - parked).min(parked), self.fanout);",
                       "let (now, later) = split(wanted.saturating_sub(workers - parked).min(parked) + 1, self.fanout);", record_park, check_park_traces)),
    ]


def main(argv):
    tla_jar = jar()
    failed = []
    for model in MODELS:
        passed, out = tlc(tla_jar, HERE, model)
        states = next((line for line in reversed(out.splitlines()) if "distinct states found" in line), "")
        print(f"{model}: {'PASS' if passed else 'FAIL'} {states.strip()}", flush=True)
        if not passed:
            failed.append(model)
            print(out[-3000:])
    if "--models" not in argv:
        for model, what, name, *edits in CONTROLS:
            with tempfile.TemporaryDirectory() as d:
                for f in os.listdir(HERE):
                    if f.endswith((".tla", ".cfg")):
                        shutil.copy(os.path.join(HERE, f), d)
                path = os.path.join(d, name)
                text = open(path).read()
                for old, new in zip(edits[::2], edits[1::2]):
                    if text.count(old) != 1:
                        sys.exit(f"check.py: the control's text is not in {name} once: {what}: {old!r}")
                    text = text.replace(old, new)
                open(path, "w").write(text)
                passed, out = tlc(tla_jar, d, model)
            found = next((line for line in out.splitlines() if "violated" in line or "Deadlock" in line), "")
            print(f"control {model}: {what}: {'NOT CAUGHT' if passed else 'caught'} {found.strip()}", flush=True)
            if passed:
                failed.append(f"control: {what}")
    build = os.path.join(os.path.abspath(os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")), "trace")
    finish_lines, waker_lines, park_lines = record_finish(ROOT, build), record_waker(ROOT, build), record_park(ROOT, build)
    for spec, check, lines in [("FinishTrace", check_finish_traces, finish_lines), ("WakerTrace", check_waker_traces, waker_lines),
                               ("ParkTrace", check_park_traces, park_lines)]:
        passed, said = check(tla_jar, HERE, lines)
        print(f"traces {spec}: {'PASS' if passed else 'FAIL'} {said if passed else said[:4000]}", flush=True)
        if not passed:
            failed.append(f"traces: {spec}")
    if "--models" not in argv:
        for what, passed, said in trace_controls(tla_jar, finish_lines, waker_lines, park_lines):
            print(f"control traces: {what}: {'NOT CAUGHT' if passed else 'caught'} {said.splitlines()[0]}", flush=True)
            if passed:
                failed.append(f"control: {what}")
    if failed:
        sys.exit(f"check.py: {', '.join(failed)}")
    print("check.py: every model passes, every recorded schedule is a behavior of its model, and each fails for each planted fault")


if __name__ == "__main__":
    main(sys.argv[1:])
