# Validation plan: formal methods beyond the kernel proofs

This plan says which parts of BLAKE3-Servil could be checked by a formal
tool (Lean, TLA+, a weak-memory model checker and others), in what order,
and what each stage would and would not establish. It is for the people
deciding where verification effort goes next.
[`validation-audit.md`](validation-audit.md) records what is checked today
and what a run of every check found; this plan starts from its gaps (G1 to
G7 there).

## Where the stages stand

As of November 27, 2026. Each stage's tracker issue holds its detail.

| Stage | State | What landed |
|---|---|---|
| 1, the Lean definition as an oracle (#3) | done | `tools/verify/lean/Vectors.lean` writes `test_vectors/lean_vectors.json` (138 cases); every test that reads the official vectors reads it too: the `Hasher` (`test_vectors/`), the throughput and multithreaded calls (`threads/tests/vectors.rs`), the `Pipeline` (`pipeline_pool.rs`), the C API and `b3sum` |
| 2, theorems about the algorithms (#4) | done | `tools/verify/lean/Algorithms.lean`: the incremental stack, cut and merge, rows, extended output, outboard and counters, each equal to the definition; `Pieces.lean` the `Pipeline`'s lazy fold of piece values (#21); `Credits.lean` a room's credit count at its real size (#19) |
| 3, the thread protocols in TLA+ (#5) | done | `tools/verify/tla/`: the three handshakes, round-robin turns, and six models of the `Pipeline`, each with controls; the handshakes' models checked against Shuttle's schedules of the code (trace validation, #22). Left: trace validation of the `Pipeline` models and the waker's fast path (#31) |
| 4, weak memory (#6) | open | |
| 5, `b3sum` in TLA+ (#7) | open | |
| 6, the kernels' callers (#8) | waiting on its decision | |
| 7, hax (#9) | open | |
| 8, one kernel proof in Lean (#10) | open | |

## Where the plan starts

Today the chain from BLAKE3's text to the shipped code is:

1. `c2sp/BLAKE3.md` is transcribed into `c2sp/BLAKE3/Blake3.lean`, which
   reproduces the document's traces and the official test vectors.
2. Lean proves that the compression formula the proof tools use is the
   definition's `BLAKE3_COMPRESS` (`tools/verify/lean/`).
3. Z3 proves that each assembled kernel computes that formula, within its
   harness's contract (`tools/verify/prove_*.py`).
4. Everything above the kernels (the tree walk, the `Hasher`, the pool, the
   `Pipeline`, `b3sum`, the C API) is tested against official BLAKE3 and
   mutation-tested, and unproved.

So the formal chain stops at step 3. The stages below extend it upward,
cheapest and most certain first.

## Decisions already made that this plan keeps

The quality manual
([Formal verification: what we tried and considered](quality-manual.md#formal-verification-what-we-tried-and-considered))
records these, and the plan does not reopen them without a new reason:

- **Kani and Aeneas** were used (the pool's cuts and batch tables; the tree
  walk and the `Hasher`) and set aside for their cost in proof hours and
  tools. Stage 6 proposes one narrower use of a bounded checker and asks
  for a decision before any work; no stage brings Aeneas back.
- **Loom** was replaced by Shuttle because it does not model `SeqCst`'s
  total order, and the handshakes are under one tool. Stage 4 checks weak
  memory on a model of the handshake, not by adding a second scheduler
  over the same source.
- **Miri** went with the portable kernels it ran. Not proposed.

## Tools chosen, and one left out

| Tool | Used for | Why this one |
|---|---|---|
| Lean | the definition as a test oracle; theorems about the tree algorithms; one kernel proof re-checked by Lean's kernel | already the definition's language and already installed for the proofs: no new tool |
| TLA+ (TLC) | the thread handshakes, the `Pipeline`'s loans and rooms, `b3sum`'s read and `io_uring` rules | every schedule of a small model, and liveness ("every job finishes"), neither of which Shuttle's sampled schedules give |
| herd7 | the wait handshakes under Arm's and x86's memory models | the handshake is a few-line litmus test, the shape herd7 decides exhaustively |

**Alloy is left out.** What it would model here (who holds a loan, which
room is free, which file descriptor is which) changes over time, and TLA+
already covers state that changes; a second modelling language for the same
facts would be two versions of one idea. If a purely structural question
turns up (the outboard's node layout is the nearest candidate), Lean
answers it with a proof, not a bounded search.

## Stages

Each stage is one tracker issue. Sizes are estimates from reading module
headers and the quality manual, not from attempts.

### Stage 1: the Lean definition as an oracle for the whole library

**Closes G1.** The library and the Lean definition agree today only
because each matches the official vectors.

- Build the Lean definition into a small executable that reads
  (mode, key or context, input, output length) and prints the output.
- Compare it with every entry point: `convenience`, the `Hasher`,
  `hash_each`, `Batch`, the multithreaded calls, the `Pipeline`, the C API
  and `b3sum`; all three modes; output lengths across the 64-byte block
  boundary; input lengths either side of each block, chunk and
  power-of-two subtree boundary, and each kernel's lane count.
- Controls: a wrong constant planted in a copy of the Lean, and a wrong
  merge planted in a copy of the Rust, must each fail the comparison.

**Establishes:** agreement on the lengths tried, against the definition
itself, with no official-BLAKE3 code in between.
**Does not:** prove agreement at untested lengths.
**Size:** days. The Lean runs at interpreter speed, so the length list is
chosen, not exhaustive; it belongs beside the long proofs, not in
per-commit CI.

### Stage 2: theorems about the algorithms the library uses

**Closes G2.** `Theorems.lean` proves the tree's split rule. The library
never computes the tree by that recursion: it streams, cuts and merges.
Each theorem below states that one such algorithm, written in Lean beside
the definition, equals the definition's `tree` or `output`.

1. **Incremental stack.** Feeding chunks left to right and merging
   completed subtrees on a stack gives `tree`'s root, for every chunk
   count.
2. **Cut and merge.** Cutting the chunks at any boundaries where every
   piece is a subtree of `tree`, hashing pieces independently and merging
   their values gives the same root (the pool's pieces, `hash_each`'s
   per-message merge, the 16 KiB groups).
3. **Rows.** Merging two rows of n equal subtrees lane by lane equals
   merging their condensed values (`CvStack`'s rows).
4. **Extended output.** `output root n` is a prefix of `output root m` for
   n ≤ m, and block i depends on the counter i alone (seeking).
5. **Outboard.** The pre-order list of parent nodes over 16 KiB groups is
   exactly the nodes `tree` visits at that level and above.
6. **Counters.** For inputs below 2^64 bytes no chunk counter wraps.

**Establishes:** the algorithms are right, for every input, as written in
Lean.
**Does not:** show the Rust implements those algorithms. That link is
tests: each Lean model is executable, so stage 1's harness can compare
intermediate values (stack contents, piece values) with the Rust where the
Rust exposes them to tests.
**Size:** weeks; items 1, 2 and 4 first.

### Stage 3: the thread protocols in TLA+

**Closes G5.** Shuttle runs the production source over sampled schedules
and cannot state "eventually".

- One specification per handshake (`park.rs`, `waker.rs`, `finish.rs`):
  safety (a parked worker is woken when work is published; one waiter's
  `Waker` is never read while written) and liveness under weak fairness
  (every published piece is finished; every waiting caller returns).
- One for the `Pipeline`'s resources: rooms, loans, slots and storages; a
  room is never handed back while a worker reads it, a storage is never
  reused while held, an abort frees everything.
- One for round-robin service of concurrent callers: no caller starves.
- Controls: the ten faults `tools/pipeline_model_controls.py` plants in the
  Rust are planted in the specifications too, and TLC must reject each.

**Establishes:** every schedule of the model at small sizes (two or three
workers, a few pieces), with liveness.
**Does not:** check the Rust. A specification can drift from the code;
Shuttle stays the check on the source, and each specification names the
functions it models so a reviewer can compare them.
**Size:** one to two weeks. TLC needs Java (dev-only, pinned by digest).

### Stage 4: the wait handshakes under weak memory

**Closes G6.** Shuttle treats every ordering as `SeqCst`;
`tools/check-waker-order.py` checks the compiled fences of three wait
paths on Apple Arm64.

- Write each Dekker handshake as a litmus test with its real orderings and
  fences, and decide it with herd7 under the Armv8 and x86-TSO models: the
  outcome "both sides saw nothing" must be forbidden.
- Controls: remove the fence, or weaken a `SeqCst` store to `Release`; the
  outcome must become allowed.

**Establishes:** the ordering argument in each file's header, for every
execution the architecture's model allows.
**Does not:** check that the compiler emitted those orderings (that is
`check-waker-order.py`'s job) or cover code outside the handshakes.
**Size:** days.

### Stage 5: `b3sum`'s read and ring rules in TLA+

**Closes G7.** `b3sum` is outside the mutation gate.

- `file_end.rs`: model the kernel's possible answers to each read (bytes,
  a short read, 0, `EAGAIN`, an error) on the waiting and the non-waiting
  path; check that only a waiting read's 0 ends a file and that no error
  is swallowed.
- `uring.rs` and `linux_pipe.rs`: model submission, completion, panic and
  exit; check the kernel never holds a buffer the process has freed.
- Controls: the eleven protections of `tools/b3sum_controls.py`, removed
  from the model one at a time.

**Size:** about a week. Same limits as stage 3.

### Stage 6 (decision first): the Rust callers meet each kernel's contract

**Closes G3.** Each Z3 proof holds under its harness's contract (buffer
sizes, counts, alignment). The manual states that every call the crate
makes falls within those contracts; that statement is checked by reading
and by tests, not by a tool.

Two ways to check it, and the issue asks which, if either:

- **A test-time contract check (no new tool).** Generate, from each
  harness's declared contract, an assertion the test build runs before
  each kernel call; the existing suites and mutation gate then exercise
  it. Covers the calls the tests make.
- **A bounded checker (Kani) on the call wrappers alone**, with each
  kernel replaced by a stub that asserts its contract. Covers every call
  within the bound. This brings back a tool the project set aside, for a
  narrower job than before; it needs a reason stronger than this plan
  has, such as a contract violation found by review.

**Size:** the first, about a week; the second, unknown.

### Stage 7 (experiment, time-boxed): Rust equal to the definition through hax

The manual lists hax as considered, not tried, and suited to proving Rust
equal to a specification. One week on `src/tree.rs` alone (safe Rust over
its kernels), with the kernels as axioms stated by the Z3 proofs, would
say whether stage 2's theorems can be tied to the source by proof instead
of by test. If the extraction does not get through the file in the week,
record why in the manual and close.

### Stage 8 (experiment, time-boxed): one kernel proof checked by Lean

**Narrows G4.** Today the kernel proofs trust Z3, the Python instruction
models and the JSON-to-Z3 reader. Lean's `bv_decide` proves bit-vector
goals with a certificate Lean's kernel checks. Take the smallest kernel
case (one compression), export the model's output term, and prove it equal
to `BLAKE3_COMPRESS` inside Lean. If it goes through in reasonable time,
the solver and the reader leave the trusted base for that case, and the
issue reports what the rest would cost. The instruction models stay
trusted either way.

## What no stage reaches

- BLAKE3's security: collision and preimage resistance rest on
  cryptanalysis.
- The compiler, assembler, linker, operating system and CPU.
- Speed and timing behaviour, which the benchmarks measure.
- Whether a model (stages 2 to 5) matches the code it describes, beyond
  what tests and review show.

## Rules for every stage

- **Each check is seen to fail** before it counts: the controls above, run
  and named in the commit that adds the check.
- **One command re-runs it.** Each stage adds its check to
  `tools/audit.py`, so `python3 tools/audit.py` shows the whole state.
- **Minutes, not hours, or it runs with the long proofs.** A check slower
  than a few minutes joins `tools/verify/long-proofs.sh`, not per-commit
  CI.
- **Dev-only tools, pinned.** Nothing here touches the shipped crates'
  dependencies; each downloaded tool is pinned by SHA-256 and BLAKE3.
- **A stage that does not pay is closed with its reason** in the quality
  manual's "what we tried" list.
