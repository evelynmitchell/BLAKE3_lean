#!/usr/bin/env python3
"""Check the pool's handshakes under the memory models, and that each fails for its planted faults.

    python3 tools/verify/herd/check.py

Each handshake that must not lose a wake (park.rs's park_unless against
source.rs's publish, lanes.rs's SME2 thread against the same publish,
waker.rs's register against notify_after_seqcst, and
finish.rs's wait against finished), and finish.rs's outputs made visible
by the count, is a litmus test here with its real orderings and fences,
and herd7 lists every execution the model allows. Every test's `exists`
is the outcome that loses a wake (or reads a missing output), and it must
be Never:

  NAME.litmus          C11 atomics under RC11 (rc11.cat), the language's
                       contract: what any compiler and CPU may do.
  NAME.aarch64.litmus  the instructions rustc emits for aarch64-apple-darwin
                       (LSE, RCpc), under the Arm model (aarch64.cat).
  NAME.x86.litmus      the instructions rustc emits for x86-64, under
                       x86-TSO (x86tso.cat); park and waker alone, since
                       TSO's one reordering is a store past a later load
                       (and the SME2 thread runs on Arm alone).

The Shuttle tests and the TLA+ models assume one total order of the
operations (SeqCst); these check that the orderings in the code give that
order where the handshakes need it. A test that passes proves nothing until
it is seen to fail: each control plants one fault (a fence left out, an
ordering weakened) in a copy, in a temporary directory, and herd7 must find
the outcome. The tests here are never edited.

herd7 is herdtools7 7.57, its source pinned by commit and by the SHA-256 and
BLAKE3 (checked with tools/blake3_ref.py) of its `git archive`, cloned once
into tmp/herd/herdtools7-7.57/ (or named by $HERDTOOLS7) and built there
with OCaml 4.14 or later, dune, menhir and zarith.
"""

import hashlib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import blake3_ref  # noqa: E402

HERD_URL = "https://github.com/herd/herdtools7"
HERD_TAG = "7.57"
HERD_COMMIT = "30fad543696c308c900ff8c3d668612d399c6096"
HERD_SHA256 = "d93661995d1fb67ebd14d44a69cb802883b9ee77a1b2d9fd2237b220da9c4ae2"
HERD_BLAKE3 = "2dfd39e3eb46b5d7a09e489b22b508ae5080ce1a957b5313d2e040f948b7214e"

MODELS = {"": "rc11.cat", ".aarch64": "aarch64.cat", ".x86": "x86tso.cat"}
TESTS = ["park", "sme2", "waker", "finish", "finish_outputs",
         "park.aarch64", "sme2.aarch64", "waker.aarch64", "finish.aarch64", "finish_outputs.aarch64",
         "park.x86", "waker.x86"]

# (test, the fault, [(text in the test, its replacement)]).
CONTROLS = [
    ("park", "the publisher's fence left out", [
        ("  atomic_store_explicit(published, 1, memory_order_release);\n  atomic_thread_fence(memory_order_seq_cst);\n",
         "  atomic_store_explicit(published, 1, memory_order_release);\n")]),
    ("park", "the worker's fence left out", [
        ("  int r9 = atomic_fetch_or_explicit(parked, 1, memory_order_seq_cst);\n  atomic_thread_fence(memory_order_seq_cst);\n",
         "  int r9 = atomic_fetch_or_explicit(parked, 1, memory_order_seq_cst);\n")]),
    ("sme2", "the SME2 thread's fence left out", [
        ("  atomic_store_explicit(parked, 1, memory_order_seq_cst);\n  atomic_thread_fence(memory_order_seq_cst);\n",
         "  atomic_store_explicit(parked, 1, memory_order_seq_cst);\n")]),
    ("sme2", "the publisher's fence left out", [
        ("  atomic_store_explicit(published, 1, memory_order_release);\n  atomic_thread_fence(memory_order_seq_cst);\n",
         "  atomic_store_explicit(published, 1, memory_order_release);\n")]),
    ("waker", "the caller's fence left out", [
        ("  atomic_store_explicit(state, 2, memory_order_seq_cst);\n  atomic_thread_fence(memory_order_seq_cst);\n",
         "  atomic_store_explicit(state, 2, memory_order_seq_cst);\n")]),
    ("waker", "the worker's state load Acquire", [
        ("atomic_load_explicit(state, memory_order_seq_cst)", "atomic_load_explicit(state, memory_order_acquire)")]),
    ("finish", "the bit in a word of its own, set Release and read Acquire", [
        ("{ [state]=0; }", "{ [state]=0; [sleeping]=0; }"),
        ("P0 (atomic_int* state) {\n  int r0 = atomic_fetch_or_explicit(state, 2, memory_order_seq_cst);\n",
         "P0 (atomic_int* state, atomic_int* sleeping) {\n  atomic_store_explicit(sleeping, 1, memory_order_release);\n"
         "  int r0 = atomic_load_explicit(state, memory_order_acquire);\n"),
        ("P1 (atomic_int* state) {\n  int r0 = atomic_fetch_add_explicit(state, 1, memory_order_seq_cst);\n",
         "P1 (atomic_int* state, atomic_int* sleeping) {\n  int r9 = atomic_fetch_add_explicit(state, 1, memory_order_acq_rel);\n"
         "  int r0 = atomic_load_explicit(sleeping, memory_order_acquire);\n")]),
    ("finish_outputs", "the count load Relaxed (October 24)", [
        ("atomic_load_explicit(state, memory_order_seq_cst)", "atomic_load_explicit(state, memory_order_relaxed)")]),
    ("park.aarch64", "the publisher's DMB left out and its load LDR (Relaxed)", [
        (" DMB ISH        | DMB ISH             ;", " NOP            | DMB ISH             ;"),
        (" LDAR X2,[X3]   |", " LDR X2,[X3]    |")]),
    ("sme2.aarch64", "the SME2 thread's DMB left out", [
        ("| DMB ISH        ;", "| NOP            ;")]),
    ("waker.aarch64", "the caller's DMB left out", [
        ("| DMB ISH        ;", "| NOP            ;")]),
    ("finish.aarch64", "the bit in a word of its own, STLR and LDAPR", [
        ("{ 0:X1=state; 1:X1=state; }", "{ 0:X1=state; 0:X3=sleeping; 1:X1=state; 1:X3=sleeping; }"),
        (" LDSETAL X0,X2,[X1]  | LDADDAL X0,X2,[X1]  ;",
         " STLR X0,[X3]        | LDADDAL X0,X9,[X1]  ;\n LDAPR X2,[X1]       | LDAPR X2,[X3]       ;")]),
    ("finish_outputs.aarch64", "the count load LDR (Relaxed)", [
        ("LDAR X0,[X1]  ", "LDR X0,[X1]   ")]),
    ("finish_outputs.aarch64", "the fetch_add LDADDA (Acquire, its Release half lost)", [
        ("LDADDAL X0,X9,[X1]", "LDADDA X0,X9,[X1] ")]),
    ("park.x86", "the publisher's fence left out", [
        (" XCHG [s0],ECX   |", " MOV ECX,$0      |")]),
    ("waker.x86", "the caller's store MOV (Release) and its fence left out", [
        ("| XCHG [state],EAX ;", "| MOV [state],EAX ;"),
        ("| XCHG [s1],ECX   ;", "| MOV ECX,$0      ;")]),
]


def git(src, *args, **kw):
    return subprocess.run(["git", "-C", src] + list(args), check=True, capture_output=True, **kw).stdout


def herd():
    """herd7 built from the pinned source: (its binary, its libdir)."""
    src = os.environ.get("HERDTOOLS7") or os.path.join(ROOT, "tmp", "herd", "herdtools7-" + HERD_TAG)
    if not os.path.isdir(src):
        subprocess.run(["git", "clone", "-q", "--depth", "1", "--branch", HERD_TAG, HERD_URL, src + ".part"], check=True)
        os.replace(src + ".part", src)
    commit = git(src, "rev-parse", "HEAD", text=True).strip()
    tar = git(src, "archive", "--format=tar", "HEAD")
    sha, b3 = hashlib.sha256(tar).hexdigest(), blake3_ref.blake3_hex(tar)
    if (commit, sha, b3) != (HERD_COMMIT, HERD_SHA256, HERD_BLAKE3) or git(src, "status", "--porcelain"):
        sys.exit(f"check.py: {src} is not the pinned herdtools7 (commit {commit}, SHA-256 {sha}, BLAKE3 {b3}, or edited)")
    exe = os.path.join(src, "_build", "default", "herd", "herd.exe")
    if not os.path.exists(exe):
        subprocess.run(["sh", "./version-gen.sh", src], cwd=src, check=True)
        subprocess.run(["dune", "build", "--profile", "release", "herd/herd.exe"], cwd=src, check=True)
    return exe, os.path.join(src, "herd", "libdir")


def observe(tool, directory, names):
    """herd7 on `names` (files NAME.litmus in `directory`, grouped by
    model): {name: Never, Sometimes or Always}."""
    exe, libdir = tool
    seen = {}
    for suffix, model in MODELS.items():
        files = [os.path.join(directory, n + ".litmus") for n in names if os.path.splitext(n)[1] == suffix]
        if not files:
            continue
        r = subprocess.run([exe, "-I", libdir, "-model", model] + files, capture_output=True, text=True)
        out = r.stdout + r.stderr
        if r.returncode != 0 or "Warning" in out:
            sys.exit(f"check.py: herd7 under {model}:\n{out}")
        seen.update(re.findall(r"^Observation (\S+) (Never|Sometimes|Always)", out, re.M))
    return seen


def main():
    tool = herd()
    failed = []
    seen = observe(tool, HERE, TESTS)
    for t in TESTS:
        print(f"{t}: {seen.get(t, 'not run')}")
        if seen.get(t) != "Never":
            failed.append(t)
    with tempfile.TemporaryDirectory() as d:
        names = []
        for i, (test, fault, edits) in enumerate(CONTROLS):
            with open(os.path.join(HERE, test + ".litmus")) as f:
                text = f.read()
            for old, new in edits:
                if text.count(old) != 1:
                    sys.exit(f"check.py: control {test}: {fault}: {old!r} is not in {test}.litmus once")
                text = text.replace(old, new)
            # The control's own name: herd7 reports by the test's name.
            name = test.replace(".", f"_c{i}.", 1) if "." in test else f"{test}_c{i}"
            head, rest = text.split("\n", 1)
            with open(os.path.join(d, name + ".litmus"), "w") as f:
                f.write(f"{head.split()[0]} {name}\n{rest}")
            names.append(name)
        seen = observe(tool, d, names)
        for name, (test, fault, _) in zip(names, CONTROLS):
            caught = seen.get(name) in ("Sometimes", "Always")
            print(f"control {test}: {fault}: {'caught' if caught else 'MISSED'}")
            if not caught:
                failed.append(f"control {test}: {fault}")
    if failed:
        sys.exit("check.py: failed: " + ", ".join(failed))
    print(f"{len(TESTS)} tests forbid their outcome; {len(CONTROLS)} controls caught")


if __name__ == "__main__":
    main()
