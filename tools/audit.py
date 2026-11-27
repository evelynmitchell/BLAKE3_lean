#!/usr/bin/env python3
"""Re-run this tree's validation checks, one by one, and report each.

    python3 tools/audit.py                  # the quick checks (minutes each)
    python3 tools/audit.py --long           # the machine-code proofs too (hours, up to 24 GB)
    python3 tools/audit.py NAME...          # the named checks alone
    python3 tools/audit.py --list           # every check, its tier and what it needs

Each check is a command this repository already documents (CONTRIBUTING.md,
tools/verify/README.md); this file adds none, it maps each layer of
docs/validation-audit.md to the command that checks it. Unlike
tools/check-builds.sh and tools/verify/long-proofs.sh, which gate a landing
and stop at the first failure, a run here goes on past a failure and
past a check this machine cannot run (no Lean, no Z3, the wrong CPU, too
little memory), and says which was which:

    PASS      the command exited 0
    FAIL      it exited otherwise
    TIMEOUT   it ran past its limit and was stopped, with all it started
    SKIPPED   this machine lacks what the check needs (the report names it)

Logs go to tmp/audit/COMMIT/NAME.txt and the table to
tmp/audit/COMMIT/report.md. The exit status is 0 only when every selected
check passed, 1 when one failed or timed out, and 3 when none did but one
was skipped: a skipped check has checked nothing.
"""

import os
import platform
import shutil
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

NEXTEST = "cmd:cargo-nextest"
# The Lean definition's vectors, rewritten and compared with the committed copy
# the Rust tests read (test_vectors/lean_vectors.json).
LEAN_VECTORS = ("(cd tools/verify/lean && lake build vectors && .lake/build/bin/vectors ../../../test_vectors/lean_vectors.json)"
                " && git diff --exit-code test_vectors/lean_vectors.json")
SHUTTLE = "--test shuttle_finish --test shuttle_park --test shuttle_waker --test shuttle_pipeline"


def check(name, layer, command, needs=(), cwd=".", tier="quick", minutes=30):
    return {"name": name, "layer": layer, "command": command, "needs": tuple(needs), "cwd": cwd, "tier": tier,
            "minutes": minutes}


def prove(name, command, needs=(), minutes=240):
    return check(name, "Machine-code proofs (Z3)", f"python3 tools/verify/{command}", ("py:z3", "cmd:clang", *needs),
                 tier="long", minutes=minutes)


# A need is "cmd:PROGRAM" (on PATH), "py:MODULE" (importable), "target:TRIPLE"
# (a Rust standard library installed for it), "arch:MACHINE" (this CPU), or
# "mem:GIGABYTES" (this machine's memory, at least).
ARM_AS = "cmd:aarch64-linux-gnu-as"
CHECKS = [
    check("lean_spec", "Lean specification", "python3 c2sp/BLAKE3/check.py", ["cmd:lake"]),
    check("lean_emit", "Lean specification",
          "python3 tools/verify/lean/emit.py && git diff --exit-code tools/verify/lean/compress.json tools/verify/lean/Generic.lean",
          ["cmd:lake"]),
    check("lean_vectors", "Lean specification", LEAN_VECTORS, ["cmd:lake"]),
    check("proof_helpers", "Machine-code proofs (Z3)", "python3 -m unittest discover -s tools/verify -p 'test_*.py'",
          ["py:z3"]),
    check("unsafe_reasons", "unsafe Rust", "python3 tools/unsafe_reasons.py"),
    check("core_tests", "Rust tests", "cargo nextest run --release --lib --tests", [NEXTEST]),
    check("threads_tests", "Rust tests", "cargo nextest run --release", [NEXTEST], cwd="threads"),
    check("test_vectors", "Rust tests", "cargo nextest run --release --manifest-path test_vectors/Cargo.toml", [NEXTEST]),
    check("b3sum_tests", "Rust tests", "cargo nextest run --release --manifest-path b3sum/Cargo.toml", [NEXTEST]),
    check("capi_tests", "Rust tests", "cargo nextest run --release --manifest-path capi/Cargo.toml",
          [NEXTEST, "cmd:cargo-capi", "cmd:pkg-config"]),
    check("shuttle", "Thread schedules", f"RUSTFLAGS='--cfg shuttle' cargo test --release {SHUTTLE}", cwd="threads"),
    check("pipeline_controls", "Thread schedules", "python3 tools/pipeline_model_controls.py", minutes=60),
    check("waker_order", "Thread schedules", "python3 tools/check-waker-order.py", ["target:aarch64-apple-darwin"]),
    check("tla_handshakes", "Thread schedules", "python3 tools/verify/tla/check.py", ["cmd:java"], minutes=30),
    check("b3sum_controls", "b3sum I/O", "python3 tools/b3sum_controls.py", [NEXTEST], minutes=60),
    prove("prove_hybrid", "prove_hybrid.py", [ARM_AS]),
    prove("prove_sme2", "prove_sme2.py chunks chunks_at messages parents xof chunks_x2 every parents_every xof_every "
          "messages_every x2_every", [ARM_AS]),
    prove("prove_x86", "prove_x86.py", ["mem:24"], minutes=720),
    prove("prove_x86_loop", "prove_x86_loop.py"),
    prove("prove_output", "prove_output.py"),
    prove("prove_output8", "prove_output8.py"),
    prove("prove_output_aarch64", "prove_output_aarch64.py", [ARM_AS]),
    prove("prove_packed_x86", "prove_packed_x86.py"),
    prove("prove_packed_aarch64", "prove_packed_aarch64.py", [ARM_AS]),
    prove("prove_counter_x86", "prove_counter_x86.py"),
    prove("prove_counter_aarch64", "prove_counter_aarch64.py", [ARM_AS]),
    prove("proof_mutants", "mutants.py", [ARM_AS]),
    prove("cross_check_arm", "cross_check.py", ["arch:aarch64"], minutes=60),
    prove("cross_check_x86", "cross_check_x86.py", ["arch:x86_64"], minutes=60),
    check("mutants", "Tests of the tests", "python3 tools/mutants/check.py --whole", [NEXTEST, "cmd:cargo-mutants"],
          tier="long", minutes=240),
]


def memory_gb():
    return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") // 2**30


def missing(need):
    """What this machine lacks for `need`, or None."""
    kind, _, what = need.partition(":")
    if kind == "cmd":
        return None if shutil.which(what) else f"no `{what}` on PATH"
    if kind == "py":
        found = subprocess.run([sys.executable, "-c", f"import {what}"], capture_output=True).returncode == 0
        return None if found else f"no Python module `{what}`"
    if kind == "target":
        libdir = subprocess.run(["rustc", "--print", "target-libdir", "--target", what], capture_output=True, text=True)
        found = libdir.returncode == 0 and os.path.isdir(libdir.stdout.strip())
        return None if found else f"no Rust standard library for {what} (`rustup target add {what}`)"
    if kind == "arch":
        machine = platform.machine().replace("arm64", "aarch64")
        return None if machine == what else f"needs a {what} CPU (this is {machine})"
    if kind == "mem":
        return None if memory_gb() >= int(what) else f"needs {what} GB of memory (this has {memory_gb()})"
    raise ValueError(f"audit: unknown need {need!r}")


def run_one(c, logs):
    """(status, seconds, note) for one check, its output in logs/NAME.txt."""
    lacks = [m for m in map(missing, c["needs"]) if m]
    if lacks:
        return "SKIPPED", 0, "; ".join(lacks)
    start = time.monotonic()
    with open(os.path.join(logs, c["name"] + ".txt"), "wb") as log:
        # A session of its own, so a check that runs past its limit is
        # stopped with every process it started.
        p = subprocess.Popen(c["command"], shell=True, cwd=os.path.join(ROOT, c["cwd"]), stdout=log,
                             stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            code = p.wait(timeout=c["minutes"] * 60)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            return "TIMEOUT", int(time.monotonic() - start), f"stopped after {c['minutes']} min"
    return ("PASS", int(time.monotonic() - start), "") if code == 0 else (
        "FAIL", int(time.monotonic() - start), f"exit {code}")


def run(checks, logs, out=sys.stdout):
    """Run `checks`, write logs/report.md, and return the exit status."""
    os.makedirs(logs, exist_ok=True)
    rows = []
    for c in checks:
        print(f"== {c['name']}: {c['command']}", file=out, flush=True)
        status, seconds, note = run_one(c, logs)
        print(f"   {status} {note}".rstrip(), file=out, flush=True)
        rows.append((c, status, seconds, note))
    lines = ["| Check | Layer | Result | Time | Note |", "|---|---|---|---|---|"]
    for c, status, seconds, note in rows:
        lines.append(f"| `{c['name']}` | {c['layer']} | {status} | {seconds // 60}m{seconds % 60:02d}s | {note} |")
    with open(os.path.join(logs, "report.md"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n" + "\n".join(lines), file=out)
    statuses = {status for _, status, _, _ in rows}
    return 1 if statuses & {"FAIL", "TIMEOUT"} else 3 if "SKIPPED" in statuses else 0


def main(argv):
    flags = {a for a in argv if a.startswith("--")}
    names = [a for a in argv if not a.startswith("--")]
    known = {c["name"] for c in CHECKS}
    if flags - {"--long", "--list"} or set(names) - known:
        sys.exit(__doc__)
    if "--list" in flags:
        for c in CHECKS:
            print(f"{c['name']:22} {c['tier']:6} {c['layer']:26} needs: {' '.join(c['needs']) or '-'}")
        return 0
    if names:
        checks = [c for c in CHECKS if c["name"] in names]
    else:
        checks = [c for c in CHECKS if c["tier"] == "quick" or "--long" in flags]
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
    logs = os.path.join(ROOT, "tmp", "audit", commit)
    status = run(checks, logs)
    print(f"\nlogs: {logs}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
