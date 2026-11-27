#!/usr/bin/env python3
"""Check the TLA+ models of the pool's handshakes, and that each fails for its planted faults.

    python3 tools/verify/tla/check.py              # every model, then every control
    python3 tools/verify/tla/check.py --models     # the models alone

The models (Finish.tla, Waker.tla, Park.tla) state threads/src/finish.rs,
waker.rs and park.rs one atomic operation an action, and TLC checks every
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
MODELS = ["Finish", "Waker", "MCPark", "MCParkLeave"]

# (model, what the fault is, file, text to find once, its replacement)
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


def tlc(tla_jar, directory, model):
    """TLC on `model` in `directory`: (passed, its output's last lines)."""
    with tempfile.TemporaryDirectory() as meta:
        r = subprocess.run(["java", "-XX:+UseParallelGC", "-cp", tla_jar, "tlc2.TLC", "-workers", "auto", "-deadlock",
                            "-nowarning", "-metadir", meta, "-config", model + ".cfg", model],
                           cwd=directory, capture_output=True, text=True)
    out = r.stdout + r.stderr
    passed = r.returncode == 0 and "Model checking completed. No error has been found." in out
    return passed, out


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
        for model, what, name, old, new in CONTROLS:
            with tempfile.TemporaryDirectory() as d:
                for f in os.listdir(HERE):
                    if f.endswith((".tla", ".cfg")):
                        shutil.copy(os.path.join(HERE, f), d)
                path = os.path.join(d, name)
                text = open(path).read()
                if text.count(old) != 1:
                    sys.exit(f"check.py: the control's text is not in {name} once: {what}")
                open(path, "w").write(text.replace(old, new))
                passed, out = tlc(tla_jar, d, model)
            found = next((line for line in out.splitlines() if "violated" in line or "Deadlock" in line), "")
            print(f"control {model}: {what}: {'NOT CAUGHT' if passed else 'caught'} {found.strip()}", flush=True)
            if passed:
                failed.append(f"control: {what}")
    if failed:
        sys.exit(f"check.py: {', '.join(failed)}")
    print("check.py: every model passes, and fails for each planted fault")


if __name__ == "__main__":
    main(sys.argv[1:])
