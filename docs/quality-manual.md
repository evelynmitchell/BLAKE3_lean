# The quality manual: every check, and how to run it

This manual is for experts and maintainers: it lists every step we have
taken to make blake3-servil compute correct digests and stay
memory-safe, with the command that reproduces it, what it rests on, the
bugs it found, and what formal verification we have tried. For the
overview, read [QUALITY.md](../QUALITY.md) first; for the organization-wide
Servil Software Factory standards (stateful-type programming style,
supply-chain risk mitigation, cross-family review, wall-clock gate
discipline, and release promotion rules), see the
[Servil Software Factory Manual](https://github.com/servil-software-factory).

## What runs where

| Platform | Its kernels | Checked |
|---|---|---|
| 64-bit Arm: Apple Silicon, Linux and macOS | generated assembly: NEON with integer lanes, and SME2 on Apple M4 and later (tested natively on Apple M6) | **proved** at every block and group count, and tested |
| x86-64: Linux | BLAKE3-Servil's generated assembly: whole chunks with a partial one, the chunk root, and on AVX-512 32 whole chunks or 16 parent nodes at once (dispatched on AMD Zen 5 and later) | **proved** for every input, and tested |
| | upstream's assembly, its symbols renamed and its batch kernels' loads kept within each input (bug 8, below) | **proved** at every shape the crate calls (below), and tested |

## Protections and their limits

The preferred order is to eliminate a dangerous state, express the
remaining obligations in types, and fail stop on a cheaply detectable
violation. Tests then attack those specific obligations with bounded,
reproducible cases. Running successful hashing for longer is not the
release's measure of assurance.

| Hazard | Protection | What the evidence does not establish |
|---|---|---|
| Wrong kernel output, out-of-bounds access, secret-dependent branch/address | proofs over assembled kernels under stated contracts; planted bad kernels rejected | correctness of all Rust callers, every toolchain's output, or the processor |
| Worker reads state after its owner frees it | Pipeline worker-visible state lives for the process | correct reuse or synchronization of that state |
| A wait loses a wake or races on a waker | Shuttle checks the production finish/park/waker modules; `tools/check-waker-order.py` compiles the Apple Arm64 wait handshakes (`WakerSlot`, `Park`, `sme2_serve`) and verifies their fences against `RCpc` loads, rejecting unfenced controls; herd7 decides each handshake as a litmus test under RC11, the Arm model and x86-TSO (`tools/verify/herd/`) | every possible schedule, or weak-memory paths outside those handshakes |
| The Pipeline hands a result, a Room or a storage over too early, or loses a wake | Shuttle runs the whole of `pipeline.rs` against a stand-in pool; ten planted faults each make that model fail | schedules not tried, weak-memory execution, and the pool itself, which the model replaces |
| An `unsafe` block rests on a reason no one wrote down | every `unsafe` block across all five shipped crates and build scripts carries a `// Sound:` comment verified by `tools/unsafe_reasons.py` (0 undocumented blocks); `tools/counts.py` blocks rising counts of undocumented `unsafe`, `debug_assert!`, and narrowing-cast allows | that each stated reason is true: they are read by people and by the audits, not proved |
| Kernel still writes an I/O buffer after error recovery frees it | failed `io_uring_enter` aborts before recovery or unwind; a ring dropped with reads in flight aborts; a panic in `b3sum` aborts | every other lifetime or cancellation path |
| File name replaced after the file is opened | every path hashes the file already open; direct reads reopen that descriptor through procfs | a coherent snapshot against concurrent writes to that inode: a file changed while it is hashed can give the hash of bytes it never held (`b3sum/README.md`, #443) |
| Incomplete output, or empty verification input, reported as success | output errors propagated; each checkfile must contain a line, and each invalid line fails | complete directory verification or authentication of the expected digests |
| A tree built from parts that are not BLAKE3's subtrees, or joined in the wrong place, gives a hash that is no BLAKE3 hash | `TreeHasher` names a whole subtree by level and index and types the message's last subtree apart (`Cv`, `LastCv`); each value carries its place, and every join and the root compare places and the message's length in every build. `tests/tree_shape.rs`: 4,032 trees equal official BLAKE3, each wrong shape refused; within 16 chunks, every pairing of values (9,889) is taken if and only if a rule written apart from the library's makes the two children of one parent; three examples must fail to compile, each for its named reason | that the bytes handed over are the message's bytes at the place named; a place a program gives a stored value itself (`Cv::at`) |
| A `b3sum` protection lost in a later change | `tools/b3sum_controls.py` takes eleven of them out one at a time; the test for each must fail | protections it does not list; `b3sum` is outside the mutation gate |

The rows from the Pipeline's model on are additions for 0.10.0. The I/O
ones change production behavior; their fault controls are described below.

## What is new, and so where the risk is

Most of the risk is in what this implementation adds to the published
algorithm:

- AArch64 kernels: SME2 assembly for Apple M4 and later
  (`c/blake3_sme2_aarch64.S`), and integer + NEON kernels generated by
  `tools/gen_neon_hybrid.py` and `tools/gen_sme2_hybrid.py`;
- x86-64 kernels that hash whole chunks and a partial one in one pass,
  four lanes on SSE4.1, eight on AVX2, and zero-spill EVEX AVX-512F+VL
  at four, eight, and sixteen lanes, generated by `tools/gen_x86.py`
  (`c/blake3_partial_x86-64_unix.S`, `src/ffi_partial.rs`); a kernel that
  hashes an input of one chunk or less to its root in one call, generated
  by `tools/gen_x86_chunk_root.py` (`c/blake3_chunk_root_x86-64_unix.S`,
  `src/ffi_chunk_root.rs`); on AVX-512, kernels that hash 32 whole chunks
  or 16 parent nodes at once, generated by `tools/gen_avx512_32.py`
  (`c/blake3_avx512_32.S`, `src/ffi_avx512_32.rs`), where groups of that
  size take them and upstream's kernel the rest, on CPUs where they pay
  (`platform::wide_cpu`: AMD Zen 5 and later); and batches across
  messages on upstream's kernels (`src/many.rs`);
- a pool of worker threads for multithreaded hashing, in the crate
  `blake3-servil` (`threads/src/lanes.rs`); every other item of this
  list is in `blake3-servil-core`, which that crate contains;
- batches of many messages in one call (`hash_many`, `src/many.rs`),
  collections of messages and many hashers at once (`throughput::hash_each`,
  `throughput::update_each`, `src/each.rs`);
- the Pipeline's message/room/loan lifetimes (`threads/src/pipeline.rs`);
- `b3sum`'s direct and asynchronous reads, checkfile parser and outboard
  writer (`b3sum/src/`);
- the startup self-test (`src/self_test.rs`);
- the C API (`capi/b3.h` over the crate, `capi/src/lib.rs`), tested
  through every call against the official test vectors, and from a C
  program compiled as C11 with every warning an error (`capi/tests/`).

Everything below aims at this new code. Much of it is `unsafe`: assembly,
pointer tables, uninitialised scratch buffers, and threads that share
the caller's buffers.

## Correctness: every answer checked against an independent one

**Fixed answers.** The tests compare digests with answers that come
from official BLAKE3: its published test vectors (`test_vectors/`), and
for every other sweep a fixed value in the test, a 64-bit fingerprint
of all the sweep's outputs (their fold under the self-test's FNV-1a,
`tests/common/golden.rs`), which official BLAKE3 1.8.7 generated. Regenerating them is a reviewed step, run by hand:
`BLAKE3_GOLDEN=1 cargo nextest run --no-capture` computes every case with
official BLAKE3 too, stops at the first that differs, and prints each
fold (`golden NAME: 0x...`) to write in. The folds hold the same on
every machine, so one run generates them all. (The benchmark checks no
digests; correctness is these tests' business.)

**How a test chooses its inputs.** Each test checks the cases its code
can tell apart, and only those: every branch, and every arithmetic case
that changes what the code does (a boundary such as a block's last byte,
a count either side of a threshold, a remainder of each size). The cases
come from reading the code, and each test computes its list from the
code's own constants (`BLOCK_LEN`, `CHUNK_LEN`, a kernel group's size,
the dispatch's thresholds), so a list moves with the code it covers; a
change to the code's cases changes its tests in the same commit.
Inputs within one case run the same code on different data, so they add
time and no evidence: no test enumerates every length or draws random
inputs. Assembly proofs quantify input values within their stated
coverage; the tests also check calls into them and the other platforms.

**How the choice is checked**, mechanically:

- *Branch coverage* (`cargo llvm-cov --branch`, LLVM's per-branch
  counts): a test that replaces another reaches every branch side the old
  one reached: a replacement test must reach every branch side the old
  one reached, at a fraction of the inputs.
- *Mutation testing* (`cargo mutants`): it plants the likely future bug
  (`<` for `<=`, a constant or an operand off by one, a condition
  inverted) one at a time and requires a test to fail. A mutant every test
  survives is one of three things: a missing case (the test gains it), a
  change between equally correct paths (a speed threshold, listed as
  such), or code that does nothing (removed).

**Contracts and hangs.** Types enforce preconditions first. Ordinary
contract checks use `debug_assert!` (every shipped `debug_assert!` carries
a site comment explaining why it cannot run in release builds, and
`tools/counts.py` blocks rising `debug_assert!` counts); release builds
omit those checks. Checks that cheaply prevent memory mismanagement or a
silently wrong result run in every build. A failed safety check stops the
call or the process, rather than selecting an unchecked continuation.

A mistake that would give a wrong digest with no error is made
impossible where a type can: the batch calls take a `Batch`, which lets
the program write only its messages' bytes, so the bytes past each
message, which the AArch64 kernels hash as they stand, stay zero.

Some checks use plain `assert!` in every build, guarding what a user
would otherwise never see. Some guard progress in loops: without them,
bad internal state could make a loop repeat forever, with no result and
no error. Each costs one comparison.

Most of these checks are loop variants. Meyer used that term in Design by
Contract for a quantity that decreases on every pass and cannot decrease
forever. Each verifier pass removes the node at the top of its list. Any
children put there are one level closer to the leaves. Each pass through
the `Hasher`'s staging loop consumes at least one byte. Each continuing
pass through the file-copy loop has read at least one byte. Each check
costs one comparison per pass.

A panic on a pool worker ends the process. Otherwise, the caller waiting
for that worker's piece could wait forever.

Some mutants still hang: no test fails, and the clock stops the test.
The mutation check records them separately, each with its reason, in
`tools/mutants/timeouts-<arch>.txt`. Changed-line checks execute affected
places; ordinary whole runs skip names whose every place is a classified
hang. `--all-hangs` revisits them, and `--write` obtains current outcomes
before rewriting their rows.

The mutants profile uses the release configuration. A mutant caught only
by a debug assertion or an overflow check counts as uncaught. Release
users get no such check.

**Which tests do the catching, at what cost.** The tests run under
cargo-nextest, each in its own process; the mutants profile's per-test
deadline in `.config/nextest.toml` stops a hang. A change's run stops a
mutant's tests at the first that fails. A full map run (`--whole --map`)
runs every test on every mutant and records
each test's outcome and time at each mutant's place, and on the
unmutated tree (`tmp/mutants-last/map/tests.tsv`). From the map it
weighs the tests by cost: the cheapest set that still catches every
caught mutant (each step takes the test with the most uncaught mutants
per millisecond, so small tests come first), the tests outside it (each
a big test whose catches cheaper ones make), and the mutants only an
expensive test catches (each a small test worth writing). A failure
that names the startup self-test is the self-test's catch, whichever
test it ran in. The weighing guides
judgment: a test's worth can go beyond the mutants it catches (a
contract's `should_panic`, a hang, a shape no mutant models).

**What mutation testing finds.** A mutant whose build is byte for byte
the unmutated one, every test binary alike, cannot change what runs:
the check compares each binary's loaded bytes (`code_hash.py`), decides
it without a test, and lists it as "same code". That covers code for
another architecture and changes the optimizer erases. A survivor
whose tested build differs gets a second look (`release_same.py`): a
release build with the lines the mutant deletes left blank, since a
deleted line moves every later panic's location in the binary, and the
tested builds' incremental optimization keeps code a release build
drops. Hashing alike there, it is same code too. Every other
mutant a test survives is
listed with its reason in `tools/mutants/known-aarch64.txt` (the crate
with the pool has its own lists, in `tools/mutants/threads/`): code for
another machine (x86, a CPU without SME2 or the SHA-3 extension, one
CPU), a choice between equally correct paths (what to prefetch, a speed
threshold, how work is cut among threads, how long an idle worker
spins), or an equivalent change (`|` made `^` on flag bits that never
overlap). One group stays open: the thread pool's scheduling under
interleavings the ordinary tests leave to chance. Shuttle checks the
finish, park and waker handshakes, not all the pool's scheduling. The
assembly kernels are the proofs'.

A mutant that changes only speed is work to finish (Zooko, November 3;
BLAKE3 #219). Either a test catches it at once and the same way on every
machine, counting the work it changes (reads, ring bytes, entries,
tasks, bytes prefetched, threads woken) with no clock, or its code goes,
once the regression check reads level without it. Where the caller's
own state doesn't show the work, a counter that exists only in test
builds counts it on the caller's thread. A mutant that changes nothing
this machine runs stays listed with its reason. Code whose benefit the check
cannot see earns a measurement the check makes, or goes: a benefit
nobody can measure is not worth the code's ongoing cost (Zooko,
November 3). A deletion is tried first where its benefit is in doubt, and
the check on every target machine decides.

`tools/mutants/check.py` reruns every mutant, reruns alone any whose
outcome differs from the list (so a test that fails by chance, under
load, decides nothing), and fails on a survivor not listed, a listed one
now caught, a listed one without a reason, or a test the list names as
missing: the whole run (`--whole`), once per stable release. A change's
check, the default, tests only the mutants in the lines the change
makes, in about a minute (BLAKE3 #257). What it gives up waits for the
next whole run: a changed test's effect on other code's mutants, and a
listed survivor now caught.

**What the suites cover.** Branch coverage runs over the default,
one-CPU, and no-std builds. Most uncovered sides are the branches of
other machines (a CPU without the SHA-3 extension or without SME2,
which CI's AArch64 job runs), the pool's scheduling races, and
fail-stop arms. The aim is every
branch side of the code users run, each one reached by a test or named
as unreachable in the code, and every mutant either caught or explained;
a branch that is not worth a test is a sign the branch is not worth
keeping.

**The suites** (`src/test.rs` and each module's tests), among
them: every case of `hash_many` on every platform the CPU has, and of the
one-shot hash from one to seventeen chunks, against fixed values; every
platform's batch kernel at every input shape (1 to 16 blocks, keyed
flags, a counter whose low word overflows mid-batch, pointer tables
forward, reversed, and strided), against fixed values;
the pool's cuts and merges, its thread caps, and 32 callers at once.

**Every process checks itself before its first hash.** Every program
calls `initialize()` (or `initialize_multithreaded`) before hashing. It
hashes platform-specific fixed inputs and compares their folded outputs
with constants derived from official BLAKE3 (`src/self_test.rs`). A
mismatch aborts with std, or traps without it; a caller cannot catch the
failure and keep hashing. Tests plant a wrong last output byte in each
case and require that stop. The fold is FNV-1a, not a cryptographic
integrity check.

The cases exercise the selected kernel entries and public hashing paths.
AArch64's `l` kernels (short messages of unequal lengths) are deliberately
excluded from startup because of their cost; proofs and tests cover
them. `test_self_test_runs_every_kernel` checks the remaining entries
against the kernel tables. x86's wide and independent-output kernels
have additional cases and corruption controls. Each case's output feeds
the next input, following Niels Ferguson's suggestion; inputs use unusual
alignments and padding. Startup cost depends on the architecture and
cold code fetches; measurements are recorded beside `src/self_test.rs`.
This catches some build and hardware faults, not every later fault. A
malicious build can change the self-test too, so passing it does not
authenticate a binary.

## Memory safety

- **Guard pages** (`test::guard_pages`), on AArch64 and x86-64, Linux and
  macOS. These tests put each kernel's input, then its output, flush
  against an inaccessible page (after the buffer, then before it). A
  kernel that reads or writes a single byte outside its buffers crashes
  the test. They cover `hash`
  at every length to 2 KiB + 70 and around chunk counts up to 1025,
  `hash_many` at 15 message lengths and 20 counts, every input of a batch
  against a guard page of its own on every kernel the build and CPU have
  (1 to 17 inputs), the collection calls (`throughput::hash_each`, its
  multithreaded form, `throughput::update_each`) with each
  item in its own pages, and extended output at 10 lengths from three
  positions. `test_every_call_inside_guard_pages` takes every other
  public call that reads a caller's bytes or writes into a caller's
  places, in each mode, from 0 bytes to 1 MiB + 5: `hash_with`,
  `hash_xof`, `throughput::hash`, the Hasher's `update` and
  `finalize_each`; the key and the context string sit against pages
  too. The crate with the pool does the same for its calls
  (`test_every_multithreaded_call_inside_guard_pages`:
  `hash_multithreaded`, `update_multithreaded` and the rest). The C API has its own
  (`capi/tests/guard_pages.rs`), with the hasher's state in guarded
  memory as well. Custom guard-page global allocators (`tests/guard_alloc.rs`,
  `threads/tests/guard_alloc.rs`) back every heap allocation with trailing
  inaccessible pages during full test runs. A byte planted past an input (in `throughput::hash`)
  or past an output (in `b3_hasher_finalize_xof`) crashes them. They found
  bug 8 below as a crash.
- **On the Mac**: every suite in debug builds (overflow checks and
  debug assertions over the SME2 paths): all clean.
- **CI on other targets** (GitHub Actions): the suites on Linux x86-64
  and arm64 (without SME2, and without SHA-3 under QEMU), and macOS.
- **Coverage.** LLVM's source coverage over the library tests reaches
  93% of lines. The unexercised paths it showed became new tests (the
  guard-page tests among them). The rest is code for platforms the test
  machine lacks (x86, AArch64 without the SHA-3 extension) and
  fail-stop branches.

## Bounded checks of I/O failures

These tests exercise the actual CLI or the production syscall wrapper,
not an independent model of them. Run on Linux, with cargo-nextest:

```sh
cargo nextest run --release --manifest-path b3sum/Cargo.toml --tests \
  -E 'test(test_output_error_is_failure) | test(test_empty_checkfile_is_failure) | test(direct_reads_keep_the_open_file) | test(failed_enter_stops_before_unwinding)'
```

- `test_output_error_is_failure`: `/dev/full` returns `ENOSPC`. Plain,
  raw, extended output and checkfile modes must exit unsuccessfully and
  report an error. The plain case previously returned success. Control:
  ignore `out.flush()`'s error in `main`; the test must fail.
- `test_empty_checkfile_is_failure`: an empty named checkfile or stdin
  must fail, also with `--quiet` or after a valid checkfile. The valid
  fixture uses the published empty-input digest. Previously these runs
  exited successfully. Control: remove `ensure!(saw_line, ...)` in
  `check_one_checkfile`; the test must fail.
- `direct_reads_keep_the_open_file_when_its_path_is_replaced`: open A,
  rename it, create different bytes of the same length at A's old name,
  then hash the open handle on the direct-read path. Rename orders the
  steps; there is no race to get lucky on. Before the fix the result was
  the replacement's hash. Requires multiple available CPUs and direct
  reads on the test filesystem; the test returns early without them.
- `failed_enter_stops_before_unwinding`: call the actual `io_uring_enter`
  wrapper with an invalid descriptor in a subprocess inside
  `catch_unwind`. A refused syscall also takes this path, so permission
  to create rings is unnecessary. The child must die of `SIGABRT` and
  name the buffer-lifetime reason. Control: replace the abort in
  `uring::enter` with `None`; the child exits 0 and the test must fail.

The output, empty-checkfile and pathname tests failed on the old code.
The enter test rejected the planted continuation. These are checks of
specific faults, not evidence that all I/O failures are safe.

`python3 tools/b3sum_controls.py` repeats such controls by program, for
these four protections and seven more (the file's end on a direct read
and on a sized read, the small file's slot, the buffer sized by what was
read, the descriptor table, a ring dropped with reads in flight, and
the file already open where there is no `io_uring`): it makes the edit,
runs the test, requires the failure, and puts the file back.
`check-builds.sh` runs it before each landing.

`Uring::new` can fail before reads exist: then an ordinary read is safe.
Once SQEs have been published, a failed submission/wait may leave some
reads in flight. Returning an error previously let the callers drop
rooms or vectors those reads could still write. `submit_and_wait` now
returns no error to recover from: `EINTR` resumes with the kernel's SQ
head, and any other enter error aborts before destructors. A completion
with a negative read result is different: that read has completed and
released its buffer, so its file error is handled normally. The existing
`uring_reads_offsets_saturation_and_error_cqes` test checks successful
reads and an error CQE where the host permits rings.

Direct I/O opens `/proc/self/fd/N`, referring to the held file descriptor,
with independent flags and offset. It neither looks up the original
pathname nor changes stdin's shared flags. If that open fails (for
example, without procfs), hashing continues through the original handle.
This preserves file identity, not file contents. Concurrent writes and
truncation still require a stable input or a filesystem snapshot.

## Deep security audits before stable releases

Each stable release gets deep security audits by at least two separate
AI agents, using different leading-edge models. This is a release
practice, in addition to the executable checks above, not a claim that
any revision with passing tests has been audited.

Different models are not by themselves coverage. Before 0.10.0,
fourteen audits of one candidate, by ten models, were held against the
seven defects it was later known to have: one model reported the wrong
hash among them, in both of its runs, and the two audits this practice
then asked for, from different model families, reported none of the
seven
([the record](https://gist.github.com/johnservil/08e776af83103177001101793a538b61)).
So an audit counts as one of a release's two only when its model, with
a brief of the same form, has been run on a tree of ours that holds
known severe defects, and the release's record says what it found
there. The candidate `1b8e2847ec11a76cee7041a0901b4d6721c41c3a` is
such a tree (BLAKE3 #461 lists its defects). A "no findings" report
from an auditor with no such measure is one more review, not one of
the two.

The agents first review independently, without the other agent's
conclusions. Give each the exact source revision, the previous stable
release, the contracts and build instructions. Ask each to inspect the
implementation and changes, not merely summarize these documents. A
brief asks, and asserts nothing about the code: "is the wipe still
right, and what is a wiped value?", not "zeroization unchanged" (that
sentence stood in the brief of the fourteen audits above). The
scope includes:

- `unsafe` code, aliasing, initialization and arithmetic bounds;
- ownership and publication across workers, loans and kernel I/O;
- wrong hashes or false verification success on errors, malformed input
  and resource exhaustion;
- secret-dependent behavior, untrusted paths, release provenance,
  dependencies and the build chain.

Retain each report with the release evidence and link it from the
release's public record. A report names the agent and full model
identifier and provider, date, full audited commit, scope and methods,
and limitations. Keep the audit prompt and relevant tool commands with
it, excluding credentials and private machine details. Model responses
are not deterministic; readers should be able to repeat the inspection
and concrete checks, not expect identical model prose. Each finding names the path and violated contract, a concrete trigger
or argument, and its disposition: fix and regression check, rejection
with a reason, or an explicitly accepted residual risk. Verify claims
against the code; model agreement is not verification. Handle disclosure
of vulnerabilities affecting released versions before publishing
reproduction details.

An audit is not the only form of review. For a type that keeps state,
ask also for its contract: what a value means, the invariant every
value keeps, and each operation, trait implementations included,
checked against that. On the wrong hash above, nine models were given
the type and its grouped calls: three reported it when asked to audit
them, six when asked to write the contract and check the code against
it, and the other three of those wrote down the value that no
constructor makes.

Re-review affected findings when code changes after the audit. Review
the diff to the final version commit as well; a review of an earlier
candidate is not silently carried forward. A release with missing
reports, or unresolved credible memory-safety, wrong-result or security
findings, is not ready. The release record lists which reviews completed
and which findings were settled; a statement of this practice is not
itself audit evidence.

AI agents can share training data, errors and blind spots even when the
models differ. These reviews are not a formal proof or an independent
human security audit. We claim no such human audit.

## Source and release integrity

The full version string identifies a source commit; it does not identify
who authorized it. The release procedure keeps evidence on the exact
version commit and retains packaged sources and dependency resolution
from the publish dry-run. Install binaries from an authenticated source;
verify SHA-256 with a trusted implementation before executing a downloaded
hasher. An attacker who can replace a binary and its checksum file passes
that check; the rebuild below is the check that does not rest on the
release's own files.

Two programs check a release's artifacts against its version commit
(`CONTRIBUTING.md`, "Every artifact is a clean build of the version
commit"). `tools/release_artifacts.py` compares each crate with the
commit file by file, reads each program's build version, and holds each
`.sha256` and `.b3` files to the artifact beside them. `b3sum`'s Linux binaries and
the four crates are also reproducible: `tools/b3sum-release.sh` and
`tools/crates-release.sh` give the same bytes on any machine from the
same commit, the toolchain it names and the dependency lock it holds
(`tools/release/Cargo.lock`; a dependency changes only by a commit).
Before a release our build must equal GitHub's, byte for byte; after it
a workflow rebuilds the tag and compares what was published. The tag's
name holds the code commit's hash, the tag's commit must be that commit
with the version written in and nothing else, and on GitHub a release
tag can be neither moved nor deleted.
You can do the same with Docker (`b3sum/README.md`). A binary that
differs from your rebuild was not built from the source, whatever its
checksums say. 0.9.0's binaries predate this: they were built in
checkouts that held untracked files (#435).

What this does not cover: the C library's archive is not reproducible
and is checked by its build version alone (#436), so for the C library
build from source. A rebuild trusts the compiler, the C library and the
container image it starts from. Releases are not signed: what a release
is rests on GitHub's and crates.io's accounts and on the rebuild.

Reproducing a proof checks the machine code assembled by that run's
toolchain under its harness. A user's compiler or assembler may emit
different bytes. Startup checks exercise the user's resulting build on
fixed inputs, not all inputs, and cannot defeat a compiler or binary that
deliberately lies. Keep the source, toolchain and dependency origins in
the trust assessment. `cargo tree -e normal` (and `-e build`) in each
crate shows which packages enter that build; a dependency inventory is
not a security review of those packages.

For `b3sum --check`, expected digests must arrive through a trusted
channel. It checks listed files, not absence of additional files or
presence of omitted entries. An empty checkfile now fails, but a
partially deleted manifest may still pass. See
[`what_does_check_do.md`](../b3sum/what_does_check_do.md).

## Proofs

### What is proved

On AArch64 (Apple Silicon, and other 64-bit Arm CPUs), the integer and
NEON kernels in `c/blake3_neon_hybrid_aarch64.S` are proved at every
supported block count against [C2SP's BLAKE3 standard](https://c2sp.org/BLAKE3).
Each case covers every input, key, counter, and flags value under the
harness's memory and calling-convention contract.

The SME2 kernels in `c/blake3_sme2_aarch64.S` and
`c/blake3_sme2_hybrid_aarch64.S` are proved at the 512-bit streaming
vector length for one and two groups of sixteen chunks, the message
kernel at every length of 2 to 16 blocks, and every kernel at every
group count by induction over its group loop (`tools/verify/README.md`,
"Induction"): the checker requires that each pass leads to the next
within the loop's stated bound and that a progress rank falls without
wrapping, and every group's input bytes are symbols of their own, so a
kernel that read another group's bytes would compute other terms.
Planted errors (a group loop's counter or pointer step, a parent
kernel's strides, a block loop's step) are rejected.

The checks also examine accesses within the declared buffers, ABI
preservation, and branches and addresses independent of input bytes and
keys (the induction proofs also treat counters and their steps as
public: "Timing and secrets", below).

On x86-64, BLAKE3-Servil's five generated partial-chunk kernels
(`blake3_servil_partial_{sse41,avx2,avx512_4,avx512_8,avx512_16}`) are
proved for every input: each lane's sixteen blocks from its chaining value
and counter, with every per-lane, per-block length and flags, and the
snapshot after every block (`prove_x86.py partial`, 80 cases).
BLAKE3-Servil's chunk-root kernel (`blake3_chunk_root_x86-64_unix.S`, SSE4.1
and AVX-512 entries), which hashes an input of one chunk or less to its
root in one call, is proved for every input: 0 to 15 whole blocks before
the last, every last-block length, every mode (`prove_x86.py chunk_root`,
32 cases). BLAKE3-Servil's wide AVX-512 kernels (`c/blake3_avx512_32.S`: k32
and p32, 32 inputs with incrementing or fixed counters, and p16, 16
inputs) are proved for every input byte, key, counter, flags and last
length, at every block count from 1 to 16 and every entry alignment
(`prove_x86.py` wide cases, 48). Upstream's assembly kernels (SSE4.1, AVX2, AVX-512, under the
System V calling convention of Linux and macOS) are proved the same way,
against the same definition, as far as these cases:

- one compression (`compress_in_place`, `compress_xof`): SSE4.1 and
  AVX-512 (AVX2 has none of its own);
- `hash_many` at arbitrary counts (`prove_x86_loop.py`): 51 cases: each
  instruction set, at block lengths 1 to 16 with
  a fixed counter and at 16 blocks with an incrementing counter. Counts
  range from zero to the largest whose output and pointer table fit in
  64-bit regions. Every proof uses one symbolic entry-stack residue
  covering the four legal ABI alignments;
- `hash_many` at fixed counts (`prove_x86.py`): every count up to two
  passes of the kernel's width at 1, 2 and 16 blocks with an incrementing
  counter, and every block length at one full-width pass with one
  counter, for each instruction set (216 cases; the 57 of them
  `--representative` selects cover every block length and the first,
  full-width and two-pass counts);
- `hash_many` with two inputs at consecutive counters over 1 to 15
  blocks, on AVX2 and AVX-512 (30 cases): `pair.rs`'s
  shape, a whole chunk and a partial one side by side;
- AVX-512 `xof_many`: 1 to 32 blocks, which is how the crate calls it
  (`ffi_avx512.rs` makes one call per 32 blocks of a longer output).

Every call the crate makes into an assembly kernel, on x86-64 and on
AArch64, falls within these cases. Open: counts or shapes outside the
harnesses' stated contracts, which the crate does not call.

The Rust code (the dispatch, the tree walk, the `Hasher`, the pool, the
batch APIs) is tested, and unproved.

### How to read what is proved

**BLAKE3, as the proofs mean it.** `c2sp/BLAKE3/Blake3.lean` defines
BLAKE3 in Lean, as C2SP's standard states it. It follows `BLAKE3.md`
section by section, each definition under the standard's own text. It
mentions no implementation, so the proofs compare the kernels with the
standard itself. Its compression function (sections 2.2 to 3.3) is
generated from the standard's pseudocode, one rule per construct;
`check.py` confirms the generated text and reproduces every value in the
standard's appendix and the official test vectors. The same files are
proposed to C2SP as the standard's definitive Lean specification
([C2SP #393](https://github.com/C2SP/C2SP/pull/393)).

| Part | Statement | Checked by |
|---|---|---|
| The proofs' definition of the compression is the standard's | `tools/verify/lean/Sound.lean`: `symbolic_is_the_specifications` | Lean |
| Each completed kernel case computes that definition under its harness's contract | `tools/verify/prove_hybrid.py`, `prove_sme2.py` (with `prove_block_loop.py` and `prove_hybrid_loop.py` for the SME2 block loops), and on x86-64 `prove_x86.py`: every output word equal to the definition's, which `lean_spec.py` reads from Lean's `compress.json` | Z3 |

**What the proofs take on trust.** Lean rests on its kernel and three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The kernel
proofs prove the assembled machine code, and rest on Z3, on our model of
each AArch64 instruction they meet, on the assembler and disassembler,
and on `lean_spec.py`'s reading of Lean's `compress.json`. Each
instruction's model is checked against the CPU on random states and, for
85 of the 86 NEON and integer forms the kernels use and 19 of the 23
streaming forms, proved equal to Arm's own specification of the
architecture (Sail's Armv9.4, run by Isla); the rest (`tbl`, four moves
into a ZA tile that exhaust Isla's memory), and the matrix unit's loads
and stores, are checked against the CPU. The x86-64 proofs rest likewise on
`x86.py`'s model of each x86 instruction they meet, checked against the
CPU in CI on every change: 312 vector forms across the instruction-set
groups (81 of them memory forms) and 24 alignment-fault controls on a
GitHub machine with AVX-512 (the job's log names the CPU's features).

**How the checkers are checked.**

- **The definition against the standard.** `check.py` regenerates the
  compression function from the standard's pseudocode and reproduces
  every value in its appendix and the official test vectors; Lean proves
  the definition the Z3 proofs read equal to it (`Sound.lean`).
- **The instruction models against the CPU and against Arm.**
  `cross_check.py` and `cross_check_sme.py` run every register form the
  kernels use on the CPU from random states and compare each result with
  the model; `isla_check.py` proves the forms equal to Arm's own
  specification, and shows that planted errors in a model are caught.
  Reviewing the models found one wrong flag (an addition's carry when one
  operand is 0), now modelled as Arm defines it.
- **The proofs against wrong code.** `mutants.py` plants errors in the
  kernels (a rotation off by one, a wrong operation, a schedule entry
  read from the next byte, a loop's wrong counter or pointer step), and
  each is rejected; a planted `sorry` fails the Lean checks.

### How to run the proofs and read their verdicts

Lean (install with [elan](https://github.com/leanprover/elan); each
directory's `lean-toolchain` names the version):

```sh
python3 c2sp/BLAKE3/check.py        # the definition: C2SP's text, its appendix, the test vectors
python3 tools/verify/lean/emit.py   # the proofs' compression is the standard's (needs python3-z3)
```

Each prints, for every theorem, the axioms it depends on, and fails on
any beyond Lean's standard three, so exit status 0 means Lean has checked
every proof it builds, completely.

Z3 (an AArch64 Linux machine with Python 3 and `python3-z3`, Clang and
llvm-objdump 17 or later; details in [`tools/verify/README.md`](../tools/verify/README.md)):

```sh
python3 tools/verify/prove_hybrid.py   # every declared hybrid-kernel case
python3 tools/verify/prove_sme2.py chunks chunks_at messages parents xof chunks_x2 every parents_every xof_every messages_every x2_every
                                      # fixed-count cases and loop inductions
python3 tools/verify/mutants.py        # wrong kernels, each rejected
```

The x86-64 proofs run on any machine with Python 3, `python3-z3`, Clang and
LLVM's `ld.lld`; their instruction model is checked against the CPU by
`tools/verify/cross_check_x86.py`, in CI on every change:

```sh
python3 tools/verify/prove_x86_loop.py --workers 4
                                      # every input count, by induction
python3 tools/verify/prove_x86.py     # every declared assembled-kernel case
python3 tools/verify/prove_x86.py --representative   # a shorter selection
```

`sh tools/verify/long-proofs.sh` runs all of it after a change to a
kernel or the proof tools: every harness's complete matrix, the
planted-error controls and the Arm CPU cross-check. The harnesses report
their current case counts. A proved case states equality between the code
and the definition for every input in its contract; a failed one prints
`NOT PROVED` with what it could not prove, and the run ends with exit
status 1.

## Check it yourself

Building the shipped library crates requires only `rustc` (LLVM assembles
both x86-64 and AArch64/SME2 kernels directly via `core::arch::global_asm!`).
To run the full test and check suite (which also compiles the official
`blake3` reference oracle and `capi/` tests with a C compiler):

```sh
git clone -b main https://github.com/servil-software-factory/BLAKE3 && cd BLAKE3
cargo nextest run --release --lib --tests         # the one-thread crate
cargo nextest run --release --manifest-path threads/Cargo.toml --lib --tests
cargo nextest run --release --manifest-path b3sum/Cargo.toml
cargo test --release --doc                        # each doc example in its own process
cargo nextest run --release --manifest-path test_vectors/Cargo.toml
cargo nextest run --release --manifest-path capi/Cargo.toml   # the C API
sh tools/check-builds.sh                          # full target×feature -D warnings, Shuttle, controls, counts
python3 tools/dependency_policy.py                # cargo-deny + cargo-vet + lockfile checks
```

The tests need [cargo-nextest](https://nexte.st).

The crate is crash-only software: what still exists as a process ends (a
pool's threads, a recycled source, a test's buffers) is no fault, and no
code frees it for a checker's sake.

Timing claims are checked the same way: [bench-hashes](https://github.com/servil-software-factory/bench-hashes)
measures this implementation against the official crate and others on your machine.

## The bugs these steps found

The following bugs are fixed. Tests, coverage, review, CI, Miri (before
0.8), and the x86 proofs' model found them. Some were found during
development and never shipped. Items 9–13 concern the development of
0.10.0, including the inspection and fault controls described above. The proofs have
found none in the Arm kernels: what they found were faults in the
checking itself (an addition's carry flag modelled wrongly in the
executor, the machine-code proofs run on a build without the standard
library, a Sail library bug in Arm's snapshot that misread `dup`'s lane
(Isla #107, fixed upstream; the check applies the fix), and two bugs in
Sail's Lean translation, found by a probe since set aside), each fixed. Their
contribution is the other half: for every input, the proved parts
compute the standard's BLAKE3. The commits that introduced and fixed
each bug are in `git log`.

1. **The SME2 message kernel mishandled one-block messages**
   (`blake3_servil_sme2_hash16_messages_512` in `c/blake3_sme2_aarch64.S`).
   A one-block message was compressed twice, the second time without
   the chunk-start flag. A one-block message now starts and ends on
   its last block.
2. **`Platform::hash_many` dropped the tail of an input that was not
   whole blocks** (`src/platform.rs`). A message length that was not a
   multiple of 64 bytes lost its last partial block with no error, so
   two messages that differed only in those bytes got the same digest.
   Such a length is now a compile-time error.
3. **A batch path asserted on a CPU combination that does not exist**
   (`hash_blocks` in `src/many.rs`). On SME2 without the SHA-3
   extension, a fallback arrangement made a pointer-table length look
   like a padded group, and an assertion stopped the program. The
   function now records its own choice.
4. **A `Stream` branch would have hashed only the last buffer**
   (`finalize_handed_over`, in the stream's code of that time; the
   Pipeline has since replaced it). That state cannot
   occur once a buffer has been handed over; the branch is now a
   fail-stop `expect`.
5. **On macOS a pool could allocate after warm-up** (`threads/src/lanes.rs`).
   The pool now makes every `Mutex` and `Condvar` it needs while it
   starts, before any thread first sleeps.
6. **`update_reader` could lose bytes before an error**
   (`copy_wide` in `src/io.rs`). It returned a reader's error before
   hashing bytes the reader had already consumed. The bytes read are
   now hashed first.
7. **A data race by Rust's aliasing rules** (the stream's chain in
   `threads/src/lanes.rs`). A submitter held a reference to a whole slot while
   another thread could take that slot's buffer. Only the field is now
   touched, through the raw pointer. Miri found it, back when the crate
   had portable Rust kernels for Miri to run.
8. **The AVX2 and AVX-512 batch kernels read past an input's end**
   (`c/blake3_avx2_x86-64_unix.S`, `c/blake3_avx512_x86-64_unix.S`). Their two- and four-input paths loaded a whole
   vector from each block's quarters and kept the first 16 bytes: on an
   input's last block, up to 48 bytes past its end. Each load now reads
   only its 16 bytes. The x86 proofs' model found it; guard-page tests
   reproduce it as a crash.

9. **A worker could read freed Pipeline state** (`Shared` in
   `threads/src/pipeline.rs`, #399). An unexplained test crash led to the
   cause: a worker read the state after publishing completion, when the
   owner could already have freed it. The state now lives with its
   process-lifetime storage. No release shipped that Pipeline code.
10. **A final output error could exit successfully** (`b3sum`'s `main`).
    The buffered writer's final flush error was ignored; some check-output
    errors were ignored too. They are propagated now. `/dev/full` makes
    the failure deterministic.
11. **An empty checkfile could exit successfully** (`check_one_checkfile`).
    A file truncated to zero bytes checked nothing and still passed.
    Each checkfile must now contain at least a line; an invalid line
    also fails. This does not detect partial removal of a manifest.
12. **A direct read could hash another file at the same name**
    (`direct::read`). It opened the pathname after ordinary open and
    metadata checks. A rename and replacement between the two opens
    switched the input. Direct reads now open the original descriptor
    through procfs; outboard reads use the same mechanism.
13. **A ring error could release buffers still owned by kernel reads**
    (`Uring::submit_and_wait` and `linux_pipe`). Some callers returned or
    discarded slots on an enter failure, without confirming every read
    had completed. The wrapper now aborts there before recovery or
    unwind. The fault control verifies that stop, not a triggered
    kernel write into freed memory.
14. **A file's size could decide where it ends** (`direct::read` and
    `outboard_of`, #424). A direct read of a file whose size was a
    multiple of 2 MiB asked for no byte past it, and an outboard's small
    file was read for exactly its size. A file that had grown gave the
    hash of its first bytes. Both now take the end from a read: one more
    read after a last whole piece, and room for one more byte. The many
    small files' reads from the page cache took a read that stopped at
    the reported size for the end, to save a system call a file; they
    now read until a read gives no byte, as every other path does. 0.9.0
    had this rule and a test of it, in a source comment alone; the 0.10
    reads dropped both. The rule is now in `b3sum`'s README, where a
    user can find it and rely on it.
15. **`--keyed --outboard -` hashed nothing** (#424). The key had been
    all of standard input, and the outboard of no bytes was made in
    silence. It is an error now, as without `--outboard`.
16. **An outboard was written through whatever stood at its name**
    (`outboard_inputs`, #425). A link there led the write out of the
    directory, and an outboard others were reading was emptied first.
    An outboard is now written whole under a new name and renamed into
    place.
17. **A wrong call could crash or run the wrong kernels** (`hash_many_on`
    and `Platform`, #419). The hidden slot check ran in debug builds
    only: two bytes named as a 64-byte message crashed 0.9.0. Another
    crate could write a `Platform` the CPU lacks. The check runs in every
    build, and a `Platform` can no longer be written outside the crate.
18. **`finalize_each` gave the empty message's hash for an index named
    twice** (#420, first #310). The check was debug-only. Each hasher
    now carries a mark, and a second naming panics in every build.
19. **Safe code could free bytes the Pipeline's workers were reading,
    or get two Rooms over the same bytes** (#417, #418). An owner could
    be a borrowed slice, and a Room that took 2^30 empty commits was
    counted free while held. Owners must be `'static`, and a Room takes
    new credits before it gives out its last. The second has a test that
    starts a Room four credits from its end.

20. **`--no-mmap` did nothing** (#432). It was accepted, and files were
    mapped all the same, so a file shortened during the run could still
    stop it. Every map now goes through one function, which the option
    turns off. A test counts the maps on each path.

21. **A small file that grew could be copied past its buffer**
    (`linux_pipe`, #440). Where io_uring is not available (a container's
    default profile denies it), a file of at most 16 KiB that grew
    after its size was read had up to 16,448 bytes copied into a buffer
    of 4,096. One function now sizes the buffer by what was read and
    copies it in, on both paths, with a check in every build. A test
    fails under the old sizing.
22. **Growing the descriptor table closed a descriptor the caller had
    passed** (`grow_descriptor_table`, #441). `b3sum /dev/fd/255 other`
    lost its file, and another file opened later could take the number.
    The table is now grown by a call that never lands on an open
    descriptor. A test holds number 255 across it.
23. **A panic on a reading thread could free buffers the kernel was
    still writing** (`Uring`, #442). Dropping a ring does not wait for
    its reads. A ring now counts its reads in flight and stops the
    process if it is dropped with any, and `b3sum` is built so that a
    panic stops the process at once. A test drops a ring with a read in
    flight and expects the stop.
24. **A read error could leave `b3sum` spinning** (`stream_fd_into_rooms`,
    #437). After an error, with a finished read at the front and others
    in flight, the loop never entered the kernel, where the rest would
    complete. The error's way out is now the same code as the file's
    end. No test: it needs a device that fails a read after serving one.

25. **A tree built from parts gave a wrong hash with no error**
    (`TreeHasher`, #421). The first tree calls took any two chaining
    values as a pair, and at chunk 0 any length as a subtree, so a
    5.5 MiB message in parts of 5 MiB hashed to something that is no
    BLAKE3 hash. The calls were new and never released. They now carry
    each value's place and refuse a wrong shape, at compile time where
    Rust can and in every build otherwise; the library's pool, whose
    cut's rules were checked in debug builds alone, goes through them
    too.

Bugs 14 to 20 and 25 were found by the AI security audit of the first
0.10.0 candidate, and 24 by the second, not by the checks above. 21 to 23 were
found by reading every `unsafe` block of `b3sum`'s Linux reads and of
the Pipeline and writing its reason beside it;
`tools/unsafe_reasons.py` now fails a block there without one. 17 and
18 are in 0.9.0, reachable only outside its documented contract.

## What each check would catch

| Check | Catches | Evidence | Cannot see |
|---|---|---|---|
| Machine-code proofs of the kernels | within completed cases: a wrong result, an access outside the declared buffers, a broken calling convention, or a path depending on secret data | planted errors (a rotation off by one, an add made an xor, a read past a buffer, a loop's wrong step) are rejected (`mutants.py`); the group-induction repairs need their own controls | faults in the proof checker or instruction models; unproved cases; CPU faults |
| Instruction models against the CPU and Arm's specification | a wrong model of an instruction the proofs rely on | the CPU check found the carry-flag error; Isla rejects planted model errors | loads, branches, and calls by contract, which the executor's run of the official vectors checks |
| Mutation testing | a test suite that misses a likely bug: an operator, a bound, or a condition changed, a call or a result dropped | it found missing cases in `Hash`, the `Hasher`, `OutputReader`, `update_each`, and the self-test, and dead code, each fixed or removed; a mutant every test survives is either caught by a new test or listed with its reason | bugs unlike its changes; thread interleavings the tests leave to chance |
| Test vectors and official BLAKE3's fixed values | any wrong digest at the lengths and shapes tested, on any platform | found bugs 1 and 2 below | untested lengths and shapes |
| The Lean specification's own vectors (`test_vectors/lean_vectors.json`, which `tools/verify/lean/Vectors.lean` writes and the long proofs rewrite and compare) | a call whose digest differs from the specification at 138 lengths to 4 MiB (either side of each block, of every chunk count to 17, and of each power of two from 32 to 4096 chunks), in all three modes, some with 33 blocks of output | a chunk counter planted off by one from chunk 2048 in a copy of the Lean, and a tree split planted wrong from 2048 chunks in a copy of `src/tree.rs`, each fail the tests; the official vectors, which stop at 100 chunks, pass the first | other lengths; a fault the Lean and the library share |
| Startup self-test | a miscompiled, mislinked, or faulty-hardware kernel on the user's machine | its inputs run every kernel entry point but the ARM64 kernels for short messages of unequal lengths (a unit test checks it each run), and each case's output feeds the next, so one wrong result changes every later one | faults that appear only after startup |
| Guard pages | out-of-bounds access in the paths tested, assembly included | a byte planted past a buffer crashes the guard-page tests | paths not exercised; data races |

TLA+ models of `finish.rs`, `waker.rs` and `park.rs` (`tools/verify/tla/`,
one atomic operation an action, named after the functions they model)
are checked by TLC over every schedule of small instances: three
finishers; three rounds of the waker slot, with a second notifier;
three workers with one wake a hop and two batches, and two workers that leave at the end as
`tests/shuttle_park.rs`'s do. Beside the safety invariants (the caller
returns only with every piece finished, one thread at a time in the
waker's cell, a wake reaching a worker still looking is passed on)
they check liveness under weak fairness, which Shuttle's sampled
schedules cannot state: every waiter returns, every piece is taken,
every worker leaves. `python3 tools/verify/tla/check.py` runs them
(minutes) and plants seven faults in these three, each of which TLC must reject: a
finisher comparing the count before its piece, a caller parking on a
count read apart from its bit, a caller returning on any wake, no
re-check after registering a waker, a worker taking the waker while the
caller writes it, a worker parking without looking again, and a wake not
passed on. Three more models state the `Pipeline` (`pipeline.rs`):
`PipeRooms.tla` its rooms and their credits (a room handed out again
only once every credit is back; a piece reads its own hand-out's bytes,
and is published done only with its output written; a Room may be
dropped on another thread while the owner waits), `PipeTasks.tla` a
lent message hashed in parts and a short-message group (an event only
once every part or member is hashed; a Lent guard dropped at its event
finds its loan complete), and `PipeStorage.tla` a storage outliving
its Pipeline (on the free list only once no Pipeline or Room holds it,
and once; the next Pipeline never hands out a surviving Room's room),
each with liveness: the owner makes every commit and takes every
event, and the storage goes back on the free list. `PipeSlots.tla`
states the message slots, from `message()` to the event: each slot's
kind moves only as the code moves it (`SlotKind`, `Free` to `OpenEmpty`
to the open and waiting kinds and back), events come out in end order
and each once, an aborted message's event is `Aborted`, and no
message's event comes before its group, tasks and room pieces are done
and its Rooms' credits given back. Every wait the code does not refuse
ends (`message()`, `ready()`, and the open group the end queue's front
is in, published by a wait), over two slots and three messages, and
one slot and four, where `message()`'s refusal for untaken events is
met. Six faults fail it: events taken out of end order, an aborted
slot freed before its group finishes, a slot freed when its message is
ended rather than at its event, either wait without its refusal, and a
wait that does not publish the front's group. `PipeQueue.tla` states
the Pipeline's source (`lanes.rs`, `Source`): actions published into
a ring under its assert, taken by compare-and-swap by workers and by
the owner itself (in `block_on`, and in its spins for a piece node or
a group), the wakes (where two or more wait, `serve`'s chain, and
`wake_for_waiting` before the owner sleeps), and the rings the owner
takes from and gives back to (`free_slots`, `free_pieces`,
`local_free_rooms`). No ring is pushed past its capacity, which are
the code's (the action ring's `m * MAX_SLOT_PIECES + p_cap + g_cap`
holds every action not yet taken, for the three kinds of owner each
used to its bound); each action is run once and is the one published
at its number; the owner never sleeps on waiting actions with every
worker parked; and every action is run and the owner finishes. Six
faults fail it: a claim that does not compare `claimed` (an action
taken twice), a wait without `wake_for_waiting`, and each of the four
rings one short (the action ring's met in a smaller instance whose
owner can fill it). The code's own use is tighter (a slot is used one
way, and a short Room's piece shares its Room), so its queue holds
fewer than the ring. `PipeShort.tla` states short messages sharing a
Room and groups, and small batches: a short commit's credit on its
Room, the members of groups (`push_member`, `flush_sealed_short_rooms`,
`publish_open`), a group's task giving back its members' credits room
by room (`run_group`), groups reused by epoch (`acquire_free_group`,
`group_ready`), and `Pipeline::drop` giving back the credits of
`OpenShort` slots and of the open group's members. Each short
message's credit comes back once, and each room's count is exactly the
held Room's unspent credits and its messages' credits still out; a
group's members are read from their rooms' hand-outs; a group is
filled again only once its last epoch has completed; an event (a
batch's digests) is read only once its group wrote it; once the
Pipeline and its Room are dropped every credit is back; and every
ended message's event is taken unless the Pipeline is dropped first.
Four faults fail it: a group reused before its epoch completes, a drop
that also gives back published groups' members' credits, a group
whose metas leave out its members' rooms, and an event read before its
group completes. `Turn.tla` states
how workers choose among the registered sources (`lanes.rs`,
`run_one`): lowest slot first, and every `TURN` items one in turn from
a cursor that moves past the slot served. Beside a Pipeline that streams
in the lowest slot (always an item), every item waiting in the others is
taken (five sources, three workers, `TURN` 4). A walk always from slot
0, and a cursor that stays on the slot it served, each starve a source
and fail it. Never resetting the count after a turn passes, as it
should: every walk is then in turn, round-robin, which starves no one
and is the slower policy #241 measured.
Each of `tools/pipeline_model_controls.py`'s ten faults is planted in
them too (5 and 10 are one mechanism there), and TLC rejects each.
Dropping the owed word's generation bump (ABA) is not caught:
the schedule needs a payer's two compare-and-swaps to straddle a
publisher's add and equal payments by others, past these instances;
Shuttle's `coincident_publishers_and_payers_keep_fresh_fanout` covers
it. The models are not the code; Shuttle runs the code. The two are
tied by trace validation: `tests/shuttle_finish.rs`, `shuttle_waker.rs`
(both tests) and `shuttle_park.rs` (`owed_wakes_cascade`) log each
operation `finish.rs`, `waker.rs` and `park.rs` make (their primitives
log from inside Shuttle's own atomic step, so the log's order is the
operations'), and `check.py` checks every schedule Shuttle runs is a
behavior of its model (`FinishTrace.tla`, `WakerTrace.tla`,
`ParkTrace.tla`: a trace a deadlock where the model cannot take it):
9,000 schedules of the finish line (15 distinct), 5,000 of the waker
slot (about 60 of a caller waiting for an item and 7 of one registering
two Wakers and clearing: `Waker.tla`'s caller runs a script of such
steps, `WakerScripts.tla`) and 3,000 of the park (about 650). For each, a model
narrowed past the code and code the model does not follow (in a copy of
the tree) are rejected.

Trace validation corrected the models where they had left the code:
`Waker.tla` cleared the slot when the first check found the item done,
where `Pipeline::poll_ready` and `poll_room` return without `clear`
(leaving a stale Waker a later notify wakes, spuriously); it lacked
`install_waker`'s fast path, woke the caller before `wake_slow` stores
IDLE rather than after, and had no thread that notifies with nothing
done. `Park.tla` read the parked count and owed the rest in one step,
where `wake_for` does the two apart, and merged the park loop's load of
the bit with its park, so a token left between them went unused where
the code's park takes it. Each now follows the code, and the models'
properties and controls hold. `shuttle_waker.rs`'s first test never
takes `install_waker`'s fast path (every register after the first
follows a wake that left the slot IDLE), so a model without the fast
path passed its traces; its second test takes it, and with its traces
that model is rejected. Of the `Pipeline`'s models, `PipeRooms.tla` is
checked against `shuttle_pipeline.rs`'s
`a_wait_for_a_room_ends_when_another_thread_drops_one` (7,000
schedules, about 90 distinct): the shim's atomics know the line of
`pipeline.rs` that made each (`#[track_caller]`), so the log names
each room's count, piece flag and the waker slot with no change to
`pipeline.rs`. The traces corrected it in three places: `block_on`
polls a wait twice before it sleeps (`Repoll`, outside the fairness
assumption), a re-check that finds a room free takes it before it
clears the Waker, and the clear is a step of its own, so a notify can
land between. A model whose waits poll again only once woken, and code
whose Room drop wakes the owner on every drop, are each rejected.
`PipeTasks.tla` is checked against `lent_parts_and_a_group`, a scenario
written to its shape (a message lent in three parts, two short ones in
one group; 7,000 schedules, about 70 distinct), after the same two
corrections to its waits; a model whose parts count themselves off only
once every part has written, and code whose every part (not only the
last) wakes the owner, are each rejected. `PipeStorage.tla` is checked
against `a_storage_outlives_its_pipeline_in_its_rooms` (a Pipeline of
three Rooms dropped while two are alive on threads of their own, then
the next Pipeline of its size; 7,000 schedules, about 35 distinct) as it
was: a model whose surviving Rooms drop only once `Pipeline::drop` has
begun, and a drop that gives back an unheld room's hold as it clears
the room's count, are each rejected. `PipeShort.tla` is checked
against `short_messages_share_a_room_and_a_group` (three short messages
from one Room, one past `push_member`'s byte limit so its group goes to
the workers while the rest are written, one aborted while open; 7,000
schedules, 6 distinct): slot kinds and groups are not atomics, so the
scenario notes its own calls and the stand-in pool each publication, and
the Room's count and the groups' epochs come from the atomics. The
traces showed the model lacked that byte limit: a group is now published
full, past it (a choice), or by a wait. A model without it, and code
whose group task completes its epoch before it gives its members'
credits back, are each rejected. `PipeSlots.tla` is checked against
`messages_take_slots_and_come_out_in_end_order` (in two slots, a short
lent message in a group and a long one in parts; their events through
waits; then a third message in a freed slot, aborted while empty; 7,000
schedules, 6 distinct), the scenario's notes giving the owner's calls.
The traces showed the model's `ready()` refused a call whose front was
already done, which the code allows; a model with that refusal, and code
whose group task completes its epoch twice, are each rejected.
`PipeQueue.tla`'s queue is checked against `Source` itself: `Source` is
in its own file (`source.rs`, on its own `source_sync`), and
`tests/shuttle_source.rs` compiles it and `finish.rs` beside Shuttle's
primitives with a stand-in pool (one worker that takes, runs, and parks
behind a bit a wake clears; an owner that publishes a slot's two tasks,
a piece's action and a group's, then waits, running waiting actions
itself or not). Each schedule's takes (the load of `claimed`, of
`published`, the compare-and-swap), publications and the scenario's
notes become `PipeQueue.tla`'s actions (1,000 schedules, about 800
distinct); a model whose compare-and-swap never fails, and a
`wake_for_waiting` that wakes a worker with nothing waiting, are each
rejected. The rings `PipeQueue.tla` also states are the owner's alone
and are not traced.

Shuttle and the TLA+ models assume one total order of the operations
(`SeqCst`). Whether the code's orderings give that order where the
handshakes need it is checked by herd7 (herdtools7 7.57, its source
pinned by commit, SHA-256 and BLAKE3; `tools/verify/herd/`): each wait
handshake is a litmus test with its real orderings and fences, and its
`exists` is the outcome that loses a wake, which must be forbidden. The
handshakes are a worker parking (`park.rs`) and the SME2 thread parking
(`lanes.rs`), each against a publish (`source.rs`), a caller registering
its waker against a worker completing (`waker.rs`, `pipeline.rs`), and
the finish line's (`finish.rs`); a fifth test checks that a caller that
reads the count complete reads the finished pieces' outputs. Each is
checked under RC11 (`rc11.cat`), the language's contract, and as the
instructions rustc 1.97 emits for `aarch64-apple-darwin` (LSE atomics,
`LDAPR` Acquire loads) under the Arm model and for x86-64 under x86-TSO.
`python3 tools/verify/herd/check.py` runs the twelve tests (seconds,
after herd7 is built once) and plants sixteen faults, each of which
herd7 must allow: a fence left out on either side of each handshake,
the waker's state load weakened to `Acquire`, the finish line's bit in a
word of its own, and the finish line's count load `Relaxed`, the
ordering of the bug Sam Shackleton found on October 24.

Three results are worth knowing. The finish line's wait needs no
ordering at all: two read-modify-writes on one word are ordered by
coherence, as `finish.rs`'s header argues, and its `SeqCst` is there for
the outputs. On Apple Arm64 the code is stronger than the language
requires: with either of the park handshake's fences left out, or the
waker's state load `Acquire` (`LDAPR`), the `AL` read-modify-writes and
`LDAR` loads still forbid the lost wake, so no test on that hardware can
see these faults, which RC11 shows. And on x86-64
`fence(SeqCst)` compiles to a locked `OR` on the stack, not `MFENCE`,
and the waker's fence is redundant beside its `SeqCst` store, an
`XCHG`. The instructions were read from the compiler's output;
`check-waker-order.py` checks the wait paths' fences on every run, but
not the publisher's side or the finish line's.

Shuttle's models compile the production `finish.rs`, `park.rs`,
`waker.rs`, `pipeline.rs` and `source.rs` against its concurrency
primitives. `check-builds.sh` runs all five before each landing; `--cfg shuttle` is
required to enable them. To reproduce:

```sh
(cd threads && RUSTFLAGS="--cfg shuttle" cargo test --release \
  --test shuttle_finish --test shuttle_park --test shuttle_waker \
  --test shuttle_pipeline --test shuttle_source)
python3 tools/pipeline_model_controls.py
```

The Pipeline's model (`threads/tests/shuttle_pipeline.rs`) runs the
whole of `pipeline.rs` with a stand-in for the pool: a queue of actions
served by the model's worker threads. Its nine scenarios cover
messages through Rooms, owned and lent messages, batches, an abort, one
Pipeline after another on one storage, a Room that outlives its
Pipeline, a wait for a Room that another thread's drop ends, and a
Pipeline with no place in the pool. Every digest is compared with the
one-thread library's, a caller no one wakes is a deadlock, and each run
ends with every storage free again. The second command plants ten
faults in `pipeline.rs` one at a time (a result published before it is
written, a wake left out, a Room given back while a worker reads it, a
storage reused while held, and others) and requires the model to fail
for each. It plants them in a copy of the tree, in the build directory:
the tree itself never holds a fault. What the model
cannot see: Shuttle treats every atomic ordering as SeqCst; it tries
thousands of schedules, not all; and the pool itself is the stand-in.

`tools/b3sum_controls.py` does the same for `b3sum`, which the mutation
gate does not cover: it takes eleven protections out one at a time and
requires the test for each to fail.

`b3sum`'s reads to a file's end are a TLA+ model too
(`tools/verify/tla/FileEnd.tla`), checked by `tools/verify/tla/check.py`
against every answer Linux may give each read: bytes up to the count
asked, 0, `EINTR`, a refused probe (`EAGAIN`, `EOPNOTSUPP`, a sandbox's
`EPERM`, `EIO`), the 0 that a read that may not wait gives early on
Linux 5.9 and 5.10, a real failure (`EIO`) and a pipe's `ESPIPE`, while
the file grows by appends. It states four ways a file is read: the
warm path of `linux_pipe.rs` without a ring (`cached_then_plain`, then
`finish_sync_hash`), `hash_open_file_ex`'s small files,
`read_to_its_end`, and `direct.rs`'s pieces and the byte after them. Its
invariants are that a hash is of as many bytes as a waiting read, asked
at that offset, found the file to end at; that no hash follows a real
failure; that no failure is reported without one (not for a refused
probe, an `EINTR` or a pipe); that a buffer holds at most
`SMALL_MEM_CAP` before the read streams; and that every read ends.
Eight planted faults each fail it, two of them `b3sum_controls.py`'s
(#424's sized read and direct read); the protections that are memory or
descriptor handling, the checkfile and output, and the ring are outside
it. Each answer the kernel gives is chosen afresh, so a kernel that
repeats the early 0 at one offset forever is outside it as well. It is
a model of the code, not checked against it (stage 5, #7).

The current tests use bounded scenarios and probabilistic schedule
selection (`check_pct`), not exhaustive enumeration of arbitrary callers.
Shuttle does not model all hardware weak-memory behaviors. A passing run
is evidence about the tested scenarios and schedules, not a theorem of
all thread safety. Unlike repeated wall-clock tests, it can report and
replay a specific schedule. The ordinary suites remain under nextest;
these model tests are run with Shuttle's own scheduling.

## Formal verification: what we tried and considered

- **Lean proofs of the tree algorithms** (`tools/verify/lean/Algorithms.lean`,
  built by `tools/verify/lean/emit.py` and so by the long proofs): the
  incremental stack (every chunk pushed in turn, merging while the count
  is even), the stack's rows (a subtree held as its parts' values:
  condensing one gives its tree; two merged a layer at a time, then
  condensed, give their parent; halving is a layer), `b3sum --outboard`
  (its layers' values are the trees of their groups, its walk by index
  is the tree's pre-order of parents, and the tree over 16 KiB groups is
  the file's), cut and merge (full subtrees in place, hashed apart, pushed
  in order, then the rest), extended output (prefixes and seeking), and
  counters that do not wrap, each proved equal to `Blake3.lean`'s tree
  and output for every input, on Lean's standard axioms. They are
  proved over any merge function, so they are about the tree's shape.
  They model the algorithms, not the Rust, and the tests
  (`test_vectors/lean_vectors.json`) are what tie the Rust to the
  specification. A stack that merges one level too few, a root
  assembled in the wrong order, an output counter off by one, a layer
  of parents merging each pair the wrong way round, a condense that
  skips a layer, rows merged at mismatched widths, an outboard walk
  that skips a real parent or writes the right subtree first, a layer
  that passes its last value up where it merges, and a proof replaced
  by `sorry` each fail the build.
- **Lean proof of the Pipeline's fold of piece values**
  (`tools/verify/lean/Pieces.lean`, built by `emit.py`): `merge_pieces`,
  `push_piece`, `finish_pieces` and `fold_multi_cvs`, the lazy stack
  that settles its merges by the count's 1-bits before each push, give
  the definition's tree for every message cut into pieces of `2^b`
  chunks (a part of a message hashed in parts; a Room, whose first piece
  gives its two halves). Settled, the lazy stack is the eager stack's
  subtrees (`merge_lazy`, from `push_subtrees` and the stacks' lengths).
  A settle one merge short and a finish folding bottom first each fail
  the build; in the Rust, the first Room pushed as its left half and
  `merge_pieces` one merge short each fail the Lean-vector tests.
- **Lean proof of a Pipeline room's credit count**
  (`tools/verify/lean/Credits.lean`, built by `emit.py`): each step on a
  room's count (`init_taken`, `take_credit` with its renewal at
  `ROOM_CREDITS - 1`, `release_n` of any number, `Room::drop`) keeps it
  the Room's unspent credits plus those out to pieces and short
  messages, at `ROOM_CREDITS` = 2^30 on 64-bit words. So no step wraps
  the word, the count stays below `ROOM_CLOSING_BIT`, a held Room always
  has a credit left (a room reads free, 0, exactly when no Room or
  credit holds it), a Room's drop wakes the owner exactly when it frees
  the room, and a surviving Room's count after `Pipeline::drop` is its
  unspent credits (its drop's assertion). One assumption: at most 2^32
  credits out of a room at once (bounded by the piece nodes and slots).
  Renewal at `ROOM_CREDITS` commits, a closing bit within the counts'
  range, and a drop giving back one credit more each fail the build.
- **Kani** (bounded model checking) and **Aeneas** (safe Rust
  translated to Lean): used for the pool's cuts and batch tables (Kani)
  and the tree walk and the Hasher (Aeneas, with machine-code proofs of
  whole calls beside them), then set aside: they
  took most of the proofs' hours and tools, and mutation testing,
  coverage, and guard pages test that Rust well. The proofs keep to the
  assembly, where tests reach least.
- **Miri**: used until 0.8, on the portable Rust kernels, which users
  never ran; it cannot run assembly, so it went with them. It found
  bug 7 below.
- **Verus, Prusti, Creusot**: considered, not tried. They could
  prove the pool and the batch paths for every thread interleaving; the
  cost is annotating or restructuring the code (atomics, raw pointers,
  uninitialised memory).
- **hax to F\* or Rocq** (as used for libcrux): considered, not tried
  yet. It suits proving Rust equal to BLAKE3's specification.
- **SAW with a Cryptol specification**: considered, not tried yet. It
  proves C or LLVM code equal to a specification, and could cover the C
  NEON kernel. It does not model SME2.
- **Symbolic execution of the hybrid assembly**: done (above), with our
  own instruction models, proved equal to Arm's specification through
  Isla.
- **The SME2 assembly**: concrete-count proofs, block-loop lemmas and
  group-count inductions completed. Its models of
  streaming and ZA instructions agree with Arm's specification where Isla
  can check them and are tested against the CPU elsewhere.
- **Constant-time behaviour**: see "Timing and secrets", below.
- **Fuzzing (cargo-fuzz)**: not used. The tests enumerate every kernel
  at every input shape, count, and boundary against fixed answers, the
  paths a fuzzer of one call's input would search for. Until 0.10 they
  did not enumerate sequences of operations on a value that keeps state,
  and 0.9's wrong hash (GHSA-v237-j9h9-8pf7) was such a sequence: a
  trait implementation that left a `Hasher` no constructor makes, then a
  grouped call that relied on every `Hasher` being one a constructor
  makes. Each had tests of its own. The lifecycle tests
  (`tests/lifecycle.rs`, `threads/tests/lifecycle.rs`) now walk such
  sequences: every sequence of their steps to a small depth, and long
  seeded ones, on several values at once. A step is one thing a program
  does, for most of them one public operation with a few lengths and
  neighbours, not every argument it takes (some are several calls: the
  Pipeline's step for its next event asks, waits and asks again, and its
  step that commits a Room uses the Room's own methods on the way).
  After each step every `Hasher` in play is compared with official
  BLAKE3, the ones the step did not name included; the Pipeline's walk
  compares every event with official BLAKE3 and with the order its
  messages ended in. `tools/api.py --check` refuses a public method or
  trait implementation of those types that neither walk's list names,
  and a trait implementation of any public type whose documentation has
  no sentence for it. Both are lists of names kept complete, for the
  features the documentation is built with and for the implementations a
  crate writes for the type itself (not the automatic or blanket ones,
  nor those for references to it), one name for each trait however many
  times the type implements it (`Hash` equals three types under the one
  name `PartialEq`): they make a new operation's author name it as
  walked or give the reason it is not, and do not show that a walk tests
  what it names. Other models checked that four times, with faults of
  their own (BLAKE3 #461); each time some passed, and the walks gained
  the steps, or their file the tests, that catch them. We have not tried
  a fuzzer guided by coverage over such sequences.

## Timing and secrets

If you hash a secret, or a message that contains one, can the time the
hash takes reveal anything about it? The time may vary: with the
message's length, with what else the machine is doing, with its caches.
What matters is that it never varies with the secret. Three conditions
decide that. When all three hold, nothing about the secret shows in the
time: whoever chooses the other bytes, wherever the secret's bits sit
among them, and however often the hash is timed.

1. **Instructions and memory addresses are independent of the key and
   message bytes.** Completed assembly cases check this under each
   harness's declared public parameters: lengths, and in several induction
   harnesses counters and counter steps. A branch, address, or table index
   depending on other symbols stops the proof. The Rust callers are written
   to branch on lengths alone and are tested; their trace independence is
   outside these proofs.
2. **Each instruction takes the same time whatever values it computes
   on.** That is a promise of the CPU. BLAKE3 asks it only of additions,
   rotations, exclusive ors, loads and stores, and no CPU we know of
   varies their time with their values. Arm CPUs also make the promise
   formally, for a listed set of instructions, while data-independent
   timing (DIT) is on. This implementation leaves DIT as the calling
   thread has it — for both hashing and `Hash`/`Cv`/`LastCv` equality
   (`src/ct.rs`): turning DIT on and off per call made short messages up
   to 60% slower and digest comparisons 16–18× slower on Apple M6 and
   AmpereOne, and leaving it on would change the timing of the caller's
   own code. A program that wants Arm's promise turns DIT on in its
   threads before hashing and verifying.
   Intel's equivalent is DOITM (IA32_UARCH_MISC_CTL, bit 2), on Alder
   Lake and later. Only the operating system or firmware can set that
   MSR, for the whole machine. No call in this crate can turn it on, so a
   caller who needs it enables it at the platform level. The integer
   instructions these kernels use are on Intel's data-independent list.
   What DOITM costs on the x86 kernels is unmeasured: on our i7-12700K
   the kernel's lockdown (Secure Boot integrity mode) refuses the MSR
   write even to root.
3. **Power does not show in the timing.** A chip's power draw depends
   on the data it computes, and power can change its clock speed and so
   the time (the Hertzbleed attack, 2022). A fixed clock speed removes
   this channel; no proof about code reaches it. Apple M1 to M3 chips
   also have a prefetcher whose behaviour depends on the data in memory
   (the GoFetch attack, 2024); Apple's guidance for cryptographic code
   is to turn DIT on, as in 2.

## Stateful types, compiler ratchets, and empirical `#499` results

In November 2026 (`BLAKE3` #499), we refactored stateful types across the
workspace so invariants live in the type system rather than comments or
caller discipline: private fields, checked constructors, purpose-built
newtypes (`Domain`, `Cv`/`LastCv`, `Batch`/`Block`, `Loan`, `FileEnd`),
explicit state machines, crate `[lints]` tables denying
`unsafe_op_in_unsafe_fn`, `unused_must_use`, `unreachable_patterns`,
`clippy::correctness`, and `clippy::cast_possible_truncation` (with zero
shipped suppressions), checked `// Sound:` comments on every shipped
`unsafe` block (`tools/unsafe_reasons.py`), site comments on every
shipped `debug_assert!`, guard-page allocators, arithmetic work-count
lifecycle tests (`src/lifecycle_counts.rs`), and a non-rising complexity
ratchet (`tools/counts.py`) enforced by `check-builds.sh` and `land.py`.

To measure the effect empirically, we ran 12 independent blinded GPT
Astra security audits (`exit 0`, 2 runs × 6 areas) before (`485669d8`)
and after (`69dfdccc`) the 7-commit rollout using the exact same
immutable brief (`SHA-256 c6cd2f1c6db2487082c5156b39dc2de83f318195851557cf9c74f6c1e3f83c41`):

- **Total findings dropped 82.7% (`168 → 29`)**, with **zero
  memory-safety findings** across all 12 post-#499 runs.
- Three core and concurrency areas reached **`0 + 0 = 0` (`76 → 0`
  across 6 independent runs)**: Tree (`21 → 0`), Batch/Packed/Groups
  (`24 → 0`), and concurrent `Pipeline`/Pool/Loans (`31 → 0`).
- All 7 commits passed Apple M6 all-cells A/B regression checks (`no
  regression`), confirming zero runtime performance penalty.

## BLAKE3-Servil supply-chain & wall-clock evidence

The organization-wide standards for supply-chain risk mitigation and
wall-clock gate discipline live in the
[Servil Software Factory Manual](https://github.com/servil-software-factory).
BLAKE3-Servil's concrete checks and measured numbers:

- **Dependency & lockfile policy (`#479`, `#487`):** `python3 tools/dependency_policy.py`
  and `python3 tools/dependency_policy.py controls` (10 planted faults)
  enforce `deny.toml`, `--locked` builds, and `cargo-vet` across both the
  release workspace and standalone `b3sum/` (`b3sum` trimmed to
  `blake3-servil` + `libc`, `b3sum/Cargo.lock` 57 → 26 in `2c221200`;
  optional `serde` and direct test deps trimmed, `tools/release/Cargo.lock`
  112 → 61 and exemptions 86 → 45 in `15194e18`; `src/ct.rs` and AArch64
  runtime `libc` removed in `6366776f`, giving shipped libraries **zero
  third-party runtime dependencies** on every supported platform).
  Reproducible release verification runs via
  `tools/release_artifacts.py TAG --published --rebuilt`.
- **Wall-clock gate calibration (Nov 23, 2026):** across all 7 `#499`
  commits, cross-family GPT Astra landing reviews averaged 14 min (78
  pre-landing findings), `check-builds.sh` ~2–3 min, `x86-workhorse`
  mutants 1.5 min, and `mac-m6-build` arm64+SME2 mutants 1.7 min — while
  `arm-vm` AArch64 mutants averaged 22.4 min (7.1 hours across 19 runs,
  8/19 timeout failures, 0 unique defects) and shared-runner
  `ubuntu-24.04-arm` `pool_fairness` flaked 4 of 5 runs. Consequently,
  `tools/land.py` keeps fast native `mutants x86_64` + `mutants arm64`
  and `arm-vm` `tests aarch64` per landing (reserving `arm-vm` mutants
  for pre-release), `tools/mutants/cargo-nextest` runs `--lib` unit tests
  before `--tests` integration tests, `.config/nextest.toml` `[profile.ci]`
  skips the shared-runner wall-clock ratio test, and `cells` auto-scopes
  to benchmarked library code.

## Not yet done

No human has reviewed the code line by line, and nobody has audited it.
The test suites run on Apple M6 Macs under macOS, on an AmpereOne VM
under Linux, on x86-64 servers (AMD Zen 3 and Zen 5, Intel Ice Lake),
and on CI's hosted machines. Under Linux we do not currently have a
bare-metal SME2 host (the AmpereOne has no SME2); per-PR Linux SME2
execution coverage runs in CI via the `AArch64 Linux SME2 (QEMU 512-bit
SVL)` job (`7af3b05b`, `#412`), which verifies `HWCAP2_SME2`, `rdsvl ==
64`, the core and threads suites, and SME2 fail-stop using SHA-256 and
BLAKE3 pinned Debian `qemu-user 11.1.2`. Native Apple Silicon SME2
continues to run on macOS (`mac-m6-build` and `mac-m6-timing`).

Not yet proved: that the Rust around the kernels (the dispatch, the tree,
the `Hasher`) keeps secrets from steering a whole call, which is
tested; and upstream's x86-64 assembly beyond the cases above.
