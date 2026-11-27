#!/usr/bin/env python3
"""Check the TLA+ models of the pool's handshakes, and that each fails for its planted faults.

    python3 tools/verify/tla/check.py              # every model, then every control
    python3 tools/verify/tla/check.py --models     # the models alone

The models (Finish.tla, Waker.tla, Park.tla) state threads/src/finish.rs,
waker.rs and park.rs one atomic operation an action, and PipeRooms.tla,
PipeTasks.tla and PipeStorage.tla the Pipeline's (pipeline.rs) rooms and
their credits, messages hashed in parts, loans and groups, and a storage
outliving its Pipeline, and Turn.tla the workers' choice among sources
(lanes.rs, run_one), and TLC checks every
schedule of a small instance: the safety properties as invariants, and that
no wake is lost as a liveness property under weak fairness, which Shuttle's
sampled schedules cannot state. They model the code; they are not it. The
names of the actions follow the functions they model, for a reader to
compare.

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
MODELS = ["Finish", "Waker", "MCPark", "MCParkLeave", "PipeRooms", "PipeTasks", "PipeStorage", "Turn"]

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
    ("Waker", "the caller does not re-check after registering", "Waker.tla",
     "             /\\ cpc' = IF done > seen THEN \"clear0\" ELSE \"pending\"", "             /\\ cpc' = \"pending\""),
    ("Waker", "the worker takes the Waker while the caller writes it", "Waker.tla",
     "             /\\ IF state = \"registered\"\n                THEN state' = \"waking\"",
     "             /\\ IF state \\in {\"registered\", \"writing\"}\n                THEN state' = \"waking\""),
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


def record_finish(tree, build):
    """Run tests/shuttle_finish.rs in `tree` (a checkout), building in
    `build`: each schedule's log, a line a schedule."""
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "trace")
        env = dict(os.environ, FINISH_TRACE=out, RUSTFLAGS="--cfg shuttle", CARGO_TARGET_DIR=build)
        r = subprocess.run(["cargo", "test", "-q", "--release", "--test", "shuttle_finish", "--", "--test-threads=1"],
                           cwd=os.path.join(tree, "threads"), env=env, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"check.py: tests/shuttle_finish.rs failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
        return open(out).read().splitlines()


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


def check_finish_traces(tla_jar, models, lines):
    """Every distinct schedule in `lines` against Finish.tla as `models`
    (a directory of the .tla files) states it: (passed, what TLC said)."""
    traces = {}
    for line in lines:
        pieces, log = line.split("|", 1)
        traces.setdefault(int(pieces), set()).add(finish_trace(int(pieces), log))
    said = []
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(models):
            if f.endswith(".tla"):
                shutil.copy(os.path.join(models, f), d)
        for pieces, ts in sorted(traces.items()):
            name = f"MCFinishTrace{pieces}"
            with open(os.path.join(d, name + ".tla"), "w") as f:
                f.write(f"---- MODULE {name} ----\nEXTENDS FinishTrace\nMCTraces == <<\n" + ",\n".join(sorted(ts)) + "\n>>\n====\n")
            with open(os.path.join(d, name + ".cfg"), "w") as f:
                f.write(f"SPECIFICATION TSpec\nCONSTANTS Finishers = {pieces}\n          Target = {pieces}\n          Traces <- MCTraces\nINVARIANT Ends\n")
            passed, out = tlc(tla_jar, d, name, deadlock=True)
            found = next((line for line in out.splitlines() if "Deadlock" in line or "violated" in line), "")
            said.append(f"{pieces} finisher(s): {len(ts)} distinct schedules of {sum(1 for x in lines if x.startswith(f'{pieces}|'))}{', ' + found if found else ''}")
            if not passed:
                return False, "; ".join(said) + "\n" + out[-2500:]
    return True, "; ".join(said)


def trace_controls(tla_jar, lines):
    """The trace check fails for a model narrowed past the code, and for
    code the model does not follow: what each found (None: not caught)."""
    import pipeline_model_controls
    found = []
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(HERE):
            if f.endswith(".tla"):
                shutil.copy(os.path.join(HERE, f), d)
        path = os.path.join(d, "Finish.tla")
        text = open(path).read()
        old = "Add(f) ==    /\\ fpc[f] = \"add\""
        assert text.count(old) == 1, "the Add guard"
        open(path, "w").write(text.replace(old, old + " /\\ ~sleeping"))
        passed, said = check_finish_traces(tla_jar, d, lines)
        found.append(("Finish.tla's Add allowed only with the bit clear (narrower than the code)", passed, said))
    # The code: a copy of the tree in the build directory, never the tree.
    build = os.path.join(os.path.abspath(os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")), "trace-controls")
    tree = os.path.join(build, "tree")
    pipeline_model_controls.make_copy(tree)
    path = os.path.join(tree, "threads", "src", "finish.rs")
    text = open(path).read()
    old = "if before & SLEEPING != 0 && (before & !SLEEPING) + n == self.published.load(Ordering::SeqCst) {"
    assert text.count(old) == 1, "finished()'s condition"
    open(path, "w").write(text.replace(old, "if (before & !SLEEPING) + n == self.published.load(Ordering::SeqCst) {"))
    passed, said = check_finish_traces(tla_jar, HERE, record_finish(tree, os.path.join(build, "target")))
    found.append(("finish.rs's finished() unparks with no sleeper (the model does not)", passed, said))
    return found


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
    lines = record_finish(ROOT, os.path.join(os.path.abspath(os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")), "trace"))
    passed, said = check_finish_traces(tla_jar, HERE, lines)
    print(f"traces FinishTrace: {'PASS' if passed else 'FAIL'} {said}", flush=True)
    if not passed:
        failed.append("traces: FinishTrace")
    if "--models" not in argv:
        for what, passed, said in trace_controls(tla_jar, lines):
            print(f"control traces: {what}: {'NOT CAUGHT' if passed else 'caught'} {said.splitlines()[0]}", flush=True)
            if passed:
                failed.append(f"control: {what}")
    if failed:
        sys.exit(f"check.py: {', '.join(failed)}")
    print("check.py: every model passes, every recorded schedule is a behavior of its model, and each fails for each planted fault")


if __name__ == "__main__":
    main(sys.argv[1:])
