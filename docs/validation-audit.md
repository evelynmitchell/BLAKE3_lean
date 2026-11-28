# Validation audit: what is checked today, and what a run found

This report records which claims about BLAKE3-Servil are checked by a
tool, what a run of each check found on one machine, and where checking
stops. It is for readers deciding how far to trust the checks, and it is
the starting point of [`validation-plan.md`](validation-plan.md).

- **Commit audited:** `e1966b498bc769db3d51451a4ddc8188a19ed593` (release 0.11.0).
- **Date:** November 27, 2026.
- **Machine:** an x86-64 Linux cloud VM: 4 CPUs (Intel Xeon with AVX2 and
  AVX-512), 15 GB of memory. No Arm CPU, so nothing here ran a NEON or
  SME2 kernel.
- **Tools:** Lean 4.34.1 (the pinned toolchain), Z3 5.4.1, Rust 1.97.0,
  cargo-nextest 0.9.152 (the version `tools/ci-tools.sh` pins), Clang 18.1.3,
  GNU binutils for AArch64.

To repeat it:

```sh
python3 tools/audit.py          # the quick checks
python3 tools/audit.py --long   # the machine-code proofs and mutation testing too
python3 tools/audit.py --list   # every check and what it needs
```

`tools/audit.py` runs each documented check in turn, goes on past a
failure, and reports a check this machine cannot run as SKIPPED with what
is missing. It writes each check's log and the table below to
`tmp/audit/COMMIT/`.

## Results

The quick tier, in the order run.

| Check | Layer | Result | Note |
|---|---|---|---|
| `lean_spec` | Lean specification | PASS | |
| `lean_emit` | Lean specification | PASS | `compress.json` and `Generic.lean` regenerate to the committed bytes |
| `proof_helpers` | Machine-code proofs (Z3) | PASS | |
| `unsafe_reasons` | unsafe Rust | PASS | |
| `core_tests` | Rust tests | PASS | 264 tests |
| `threads_tests` | Rust tests | PASS | 177 tests |
| `test_vectors` | Rust tests | PASS | |
| `b3sum_tests` | Rust tests | FAIL as documented, PASS as corrected | the documented command named a library target `b3sum` does not have: finding 1 |
| `capi_tests` | Rust tests | SKIPPED | no `cargo-capi` on PATH |
| `shuttle` | Thread schedules | PASS | |
| `pipeline_controls` | Thread schedules | PASS | the model fails for each of the ten planted faults |
| `waker_order` | Thread schedules | PASS | after `rustup target add aarch64-apple-darwin`: finding 4 |
| `b3sum_controls` | b3sum I/O | PASS | |

The long tier (every `prove_*.py`, the proofs' mutants, the CPU
cross-checks, whole-crate mutation testing) was not run: see below.

## What is checked today

The checks form a chain from BLAKE3's text down to the machine code, and a
separate body of tests over the Rust.

| Link | Claim | Checked by | Kind |
|---|---|---|---|
| 1 | `Blake3.lean` says what `BLAKE3.md` says | `c2sp/BLAKE3/check.py`: sections 2.2 to 3.3 are generated from the text; the appendix's traces and the official vectors are reproduced in all three modes; quotations are verbatim | generation and test |
| 2 | The tree splits its chunks as section 4.3.2's rules say, and only that way | `Theorems.lean` (5 theorems, Lean's standard axioms) | proof |
| 3 | The compression formula the proof tools use is the definition's `BLAKE3_COMPRESS` | `tools/verify/lean/Bridge.lean`, `Sound.lean`; `emit.py` regenerates `compress.json` and compares it with the committed copy | proof |
| 4 | The Z3 reading of that formula agrees with Lean | `emit.py` evaluates it at samples Lean computed | test |
| 5 | Each assembled kernel computes that formula, stays inside its buffers, keeps the calling convention, and branches on nothing secret | `tools/verify/prove_*.py` (Z3), each within its harness's contract | proof, over models of the instructions |
| 6 | The instruction models are right | Arm: Isla against Arm's specification, and the CPU; x86-64: the CPU alone | proof (Arm, in part) and test |
| 7 | The proof tools reject wrong kernels | `tools/verify/mutants.py` | planted faults |
| 8 | The Rust library returns official BLAKE3's hashes | test vectors, official `blake3` as an oracle, lifecycle walks, mutation testing, guard pages | test |
| 9 | The thread handshakes lose no wake | Shuttle over the production source (sampled schedules, all orderings as `SeqCst`); `check-waker-order.py` for three Apple Arm64 wait paths | model checking by sampling |
| 10 | `b3sum`'s protections each have a failing test | `tools/b3sum_controls.py` | planted faults |

## Gaps

Each gap names what no tool checks today. The plan's stages refer to them
by number.

- **G1. The library is not compared with the Lean definition.** Links 1 to
  7 tie the kernels' compression to the definition. The library as a whole
  agrees with the definition only because both reproduce the official
  vectors (35 input lengths) and the library also matches official
  `blake3`. No test runs the two side by side.
- **G2. The tree algorithms are unproved.** Link 2 proves the split rule.
  The library never evaluates the tree by that recursion: it streams
  through a stack with rows (`src/hasher.rs`), cuts input into pieces for
  the pool (`threads/src/lanes.rs`), merges per message (`src/each.rs`),
  and writes an outboard (`b3sum/src/outboard.rs`). That each of these
  equals the definition's tree rests on tests.
- **G3. Nothing checks that Rust callers stay within the kernels'
  contracts.** Each proof in link 5 holds under a harness contract (buffer
  sizes, counts, alignment). The quality manual states that every call the
  crate makes falls within them; that statement is kept true by reading
  and by tests. Kani and Aeneas were tried on the Rust and set aside for
  cost (quality manual, "Formal verification: what we tried and
  considered").
- **G4. The proofs trust what is outside Lean.** `generate.py` (text to
  Lean), the JSON-to-Z3 reader (`lean_spec.py`, tested at samples), Z3
  itself, and the Python instruction models. The x86-64 models are checked
  against the CPU only; there is no check against a vendor specification
  as Isla gives for Arm.
- **G5. Thread schedules are sampled, and liveness is not stated.**
  Shuttle's `check_pct` tries thousands of schedules of bounded scenarios.
  A lost wake shows as a deadlock in a tried schedule; "every caller
  eventually returns" and "no caller starves" are not properties any tool
  checks.
- **G6. Weak memory is checked on three paths of one platform.** Shuttle
  treats every atomic ordering as `SeqCst`. `check-waker-order.py` covers
  `WakerSlot`, `Park` and `sme2_serve` as compiled for Apple Arm64.
- **G7. `b3sum` is outside the mutation gate.** Eleven named protections
  have controls; the file-end and `io_uring` state machines have tests and
  no model.

## Since this audit

The results above are of the audited commit. Since it, stages 1 to 3 of
the plan have landed ([`validation-plan.md`](validation-plan.md#where-the-stages-stand)):

- **G1 is closed** for the lengths tried: `test_vectors/lean_vectors.json`,
  written by the Lean definition, is read by every test that reads the
  official vectors (`lean_vectors`).
- **G2 is closed** for the algorithms as written in Lean
  (`tools/verify/lean/Algorithms.lean`, `Pieces.lean`). That the Rust
  implements them still rests on tests.
- **G5 is closed** for the models: TLC checks every schedule of small
  instances of the handshakes, the `Pipeline` and round-robin service, with
  liveness, and each model fails for its planted faults (`tla_models`).
  The handshakes' models are checked against Shuttle's schedules of the
  code; the `Pipeline`'s are not yet (#31).

- **G6 is closed** for the wait handshakes: the park, SME2, waker and
  finish handshakes, and the finish line's outputs, are litmus tests that
  herd7 decides under RC11, the Arm model and x86-TSO, and each fails for
  its planted faults (`herd_models`).

G3, G4 and G7 stand as written.

## Findings from this run

1. **The documented `b3sum` test command fails.** `QUALITY.md` and the
   quality manual gave
   `cargo nextest run --release --manifest-path b3sum/Cargo.toml --lib --tests`.
   Cargo stops with "no library targets found in package `b3sums`", so no
   test runs. The change that adds this report drops `--lib --tests` from
   both documents and from `tools/audit.py`; the corrected command passes.
2. **The Lean checks pass on the pinned toolchain.** `check.py` reproduced
   the traces and the official vectors and found every theorem on Lean's
   standard axioms; `emit.py` rebuilt the proofs' formula to the committed
   bytes.
3. **Nothing in this repository runs the Lean or Z3 checks automatically.**
   `.github/workflows/ci.yml` does not call them.
   `tools/verify/long-proofs.sh` does, and posts its verdict as a commit
   status on `servil-software-factory/BLAKE3` using a token file; it stops
   at once without that token. Whether the audited commit carries a
   passing "long proofs" status there was not checked.
4. **`tools/check-waker-order.py` fails with a Python traceback where the
   Rust standard library for `aarch64-apple-darwin` is not installed.**
   `tools/check-builds.sh` installs it first, so the gate is unaffected;
   run alone, the check reads as a failure of the code. `tools/audit.py`
   reports it SKIPPED with the command that installs the target.

## Not run here, and why

| Check | Why not |
|---|---|
| `capi_tests` | needs cargo-c 0.10.26 |
| every `prove_*.py`, `proof_mutants` | hours on 4 CPUs; not started in this run |
| `prove_x86` | its widest cases need up to 22 GB each; this machine has 15 GB |
| `cross_check_arm`, the SME2 cross-check | need an Arm CPU (SME2 for the second) |
| `isla_check.py` | needs Isla and Arm's Sail snapshot |
| `mutants` (whole crate) | needs cargo-mutants; about an hour on the project's hosts |
| `tools/check-builds.sh`, `tools/dependency_policy.py` | landing gates with their own tools (cross targets, cargo-deny, cargo-vet); outside this audit's list |
| doc tests, the `machine` nextest profile | not in `tools/audit.py`'s list; the second needs a machine to itself |

The first run was of the audited commit; `b3sum_tests` and `waker_order`
were run again on the commit that adds this report, which changes no
shipped code.

## Limits of this audit

- It ran the checks; it did not review the proofs' harness contracts, the
  `// Sound:` reasons, or the tests' coverage.
- A PASS is for this machine, this commit and these tool versions.
- The gaps were found by reading `QUALITY.md`, the quality manual, the
  proof tools and module headers, not by a line-by-line read of the Rust.
