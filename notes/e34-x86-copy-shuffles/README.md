# e34: strict legacy PALIGNR copy shuffle engineering

Completed bounded engineering subset, local only. No universal instruction
correctness, lifter refinement, function-correctness or complete copy-extraction
claim. No new function proofs were attempted. The only new theorems certify IL
typing; both are kernel-complete `Qed`.

Branch: `llm-proofs/e34-x86-copy-shuffles`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-1e49d7bf`.
Model/effort: `gpt-6.1-sol` / `xhigh`. Assigned service tier: `default`;
the harness does not expose a separate runtime tier attestation. No delegation.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

Nothing was installed. Existing e01/e02 dependencies and the verified Rocq
wrapper were read only. Mutable tool, Java, project, temporary and Dune state
lives only under `/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles/`.
All compiler and assumptions invocations use `ulimit -v 2000000` and
`ulimit -s 65536`; Dune uses `--cache=disabled -j1`. Java uses `-Xmx1G`, without
the tiny virtual-memory cap. No cap increases or process killing occurred.

## Inventory-first selection and scope

Read the shared plan and assigned row before implementation. `select-instructions.py`
surveys all 67 exact e01 copy extents: 720 PALIGNR occurrences, zero PSHUFB,
VPSHUFB or VPALIGNR. The SSSE3 family contributes 240 occurrences and SSSE3-back
480. `shuffle-census.json` records these counts. The selected 360 instruction
samples retain each distinct operand/immediate shape separately in both families,
with exact global/ELF addresses, bytes and owning symbol names. They are a
sample map with open fallthroughs, **not a closed copy-function map**.

Inspected actual raw pcode before choosing support: legacy XMM128 PALIGNR only.
PSHUFB, VEX shuffle variants, MMX64 and EVEX remain strict rejections. Consequently
this unit makes no claim about PSHUFB high-bit-zero/low-index masks or VEX lane
semantics. No broad CALLOTHER or Nop whitelist was added. Existing e26 vector
moves/zeroing remain available unchanged through inheritance; only the new
shuffle family is legacy128.

`pcode2coq_x64_shuffle.py` is a separate opt-in `ShuffleLifter(CopyLifter)`;
`lift-x64-shuffle.py` and `x64_shuffle_headless.py` provide its isolated, pinned,
fresh-receipt/atomic-publication driver. e26 CopyLifter, supervisor, tests, notes,
and every existing e26/e25 generated artifact are byte-identical to the assigned
checkpoint. No active e39 or other worker was imported.

The new decoder accepts exactly `66 [REX.W=0] 0F 3A 0F /r ib` with 128-bit
operands and 64-bit addressing. It independently decodes ModRM direction,
REX register extensions, SIB scale/index/base, signed displacements, RIP-relative
next-instruction addresses (including the immediate), and the full unsigned
8-bit immediate. Redundant REX and unused REX.X/B shapes, other prefixes/maps,
missing/trailing bytes, MMX, VEX, EVEX and mask state are rejected.

The raw gate requires the entire exact typed concatenation/shift DAG. It checks
all opcodes and arities, varnode widths, constant shifts, encoded immediate,
source register snapshots, destination offset, vector base metadata, memory
space/read count/effective address and final low128 write. Unique values must
be initialized, nonoverlapping, single-assignment and consumed by the final DAG;
dead nodes, partial/upper writes, reordered snapshots, GPR/flag/memory writes,
userops and arbitrary >256 reads/writes fail. The gate itself is executable
engineering code, not a proven validator.

The emitted single assignment preserves the old destination's upper128 and
extracts the low128 after shifting the 256-bit old-destination/source
concatenation right by `8*imm`. Counts 32..255 produce zero in the low128;
the full memory-source expression remains present even for zero-result counts.
This matches the legacy PALIGNR operation in Intel SDM Vol2B, PALIGNR pp4-219–222:
[primary Intel instruction reference](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf).

## Provenance and fixtures

Pinned runtime: Ubuntu glibc `2.35-0ubuntu3.12`, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`. No host-libc substitute.
The driver validates all e01 target-manifest pins, e02 Ghidra/JDK archive hashes
and the e26 compiled x86 SLEIGH/source pins. It uses Ghidra11.4.2 raw instruction
pcode in `x86:LE:64:default`, image base0x100000. Receipts hash the complete
transitive Python backend/helper set, profile, source selection, fixture source,
ELF and generated output. Fresh extraction uses fresh projects and nonce receipts.

`actual-raw.json` contains the 360 selected forward/back raw graphs.
`synthetic-raw.json` includes all accepted and deliberately rejected fixture
instructions. Captures run in fresh e34 projects against the actual pinned ELF.
Tests independently compare all recorded instruction bytes to each ELF.

`fixture/shuffles.S` assembles reproducibly with the existing GNU binutils2.42.
ELF SHA256: `dd3fd060a11db86ddf7bbdf0c530413299bdd6fbf45c2d48bb3932324d4f616a`.
The accepted `align` function has 322 PALIGNR instructions and one near RET,
a **closed 323-instruction synthetic program**, with all 256 immediates and
extra cases at 0,1,15,16,17,31,32,33,127,128,255. It includes self-aliasing,
high registers, SIB addressing, negative disp8, disp32 and RIP-relative memory.
The source bytes are read before the one destination write. The model tests
include unaligned and modulo64-wrapping addresses; these exercise IL address
semantics and do not establish architectural fault/alignment legality.

A separate excluded `reject` function assembles PSHUFB, VPSHUFB128/256,
VPALIGNR128/256, MMX PALIGNR and masked EVEX PALIGNR. Pinned Ghidra underdecodes
this unsupported EVEX instruction, leaving a spurious ADC suffix in its linear
capture. Both pieces reject; no accepted output uses those boundaries. This
is an additional reason not to extend this profile to unreviewed EVEX shapes.

`Examples/claude/lifter/x64_shuffle_fixture/` contains the closed synthetic
artifact. `x64_shuffle_pinned/` contains only 360 open instruction samples.
The latter is explicitly tagged `isolated-instruction-fixtures`, size0;
its typing theorem is not copy-function closure or correctness evidence.

## Verification and exact successful commands

Run from the worktree root. Each log records CWD, the exact shell-escaped command,
all output and its real EXIT_CODE. The following all exited0:

* `python3 notes/e34-x86-copy-shuffles/select-instructions.py` — `logs/selection.log`.
* `bash notes/e34-x86-copy-shuffles/fixture/build.sh` — `logs/fixture-rebuild.log`.
* `bash notes/e34-x86-copy-shuffles/capture.sh actual` — `logs/capture-actual-final.log`.
* `bash notes/e34-x86-copy-shuffles/capture.sh synthetic` — `logs/capture-synthetic.log`.
* `bash notes/e34-x86-copy-shuffles/reproduce.sh --update` — `logs/regenerate-complete.log`.
* `bash notes/e34-x86-copy-shuffles/reproduce.sh --check` — `logs/replay-complete.log`;
  fresh replay matches both .v/.pcode.json/receipt sets byte for byte.
* `env PYTHONDONTWRITEBYTECODE=1 TMPDIR=/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles/tmp python3 -m unittest discover -s tools/ghidra-lifter -p 'test_x64*.py' -v`
  — `logs/regressions-complete.log`; 24 tests, including original e25/e26 tests.
* `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e34-x86-copy-shuffles/check-failures.py`
  — `logs/publication.log`; harness0, four expected launcher1, two expected CLI2.
* `bash notes/e34-x86-copy-shuffles/build.sh` — `logs/dune-full.log` and
  `logs/dune-complete.log`; full selective Dune project from an empty e34 build
  directory, plus final unchanged-artifact verification. This is the e00
  selected project, not every unrelated historical proof in Examples/claude.
* `bash notes/e34-x86-copy-shuffles/print-assumptions.sh` —
  `logs/assumptions-complete.log`; all22 selected lifter typing queries.
* `python3 tools/audit-proof-source.py --base bcdd924bec65111aeb9244de21e5dba6286da845 Examples/claude/lifter/x64_shuffle_fixture Examples/claude/lifter/x64_shuffle_pinned`
  — `logs/source-complete.log`; no added or existing suspicious tokens in the two files.
* `python3 notes/e34-x86-copy-shuffles/check-ancestry.py` — `logs/ancestry-final.log`.

`build.sh` expands to the verified wrapper running:
`dune build --root "$PWD" --build-dir /home/charles/code/friends/.toolchains/e34-x86-copy-shuffles/dune-build --cache=disabled -j1`
with the mandatory virtual/stack limits. `print-assumptions.sh` uses the same
limits and `rocq compile -q -R <unit-build>/default Picinae <unit-query>/Assumptions.v`.
Scripts and verbatim logs preserve the actual paths and query construction.

The independent byte-array oracle checks all 682 accepted PALIGNR samples on40
states each: **27,280 full-state comparisons**, including every defined YMM,
GPR, flag and memory byte, zero/all-one/lane-distinct/duplicate data, aliases,
unaligned/wrapping addresses and original upper128. It separately parses assembly
operands rather than calling the production decoder. **21,406** per-node
encoding/arity/width/operand/userop mutations reject, alongside explicit
snapshot/unique/dead-node/metadata/footprint cases. The inherited copy suite adds
6,560 comparisons. These are finite regressions, not universal equivalence.

All22 queries, including both new `welltyped` theorems, report verbatim:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the existing Stdlib functional-extensionality assumption through
Picinae's typing machinery, already present in e25/e26/e11. No new admission,
Axiom or Parameter was introduced. The raw complete queries are in the log;
no functional-correctness theorem or hardware refinement is asserted.

## Boundaries and actual next frontiers

CPU SSSE3 and requisite OS/control vector state must be enabled for PALIGNR;
CPUID dispatch, XCR0/control-register feature exceptions and OS state are not
modeled. Inherited SSE/AVX moves retain their per-form feature requirements.
Assume canonical accessible, nonfaulting full-width memory, with architectural
alignment where required. Total modulo64 IL memory does not model faults,
exceptions, MMIO, concurrency, interrupts, cache/order/fences, timing or hardware
atomicity. Bits above255 are outside this projection; no hardware preservation
claim for those bits or future EVEX interaction. CET-enabled execution remains
outside the inherited e25/e26 profile. NT moves keep e26's sequential boundary.

Actual launcher attempts show further copy frontiers, not complete extraction:
`__memcpy_ssse3` first rejects indirect `JMP R9` at global0x27aca1;
`__memcpy_ssse3_back` first rejects `JNC` at global0x28021e. No output is
published for either. A first rejection does not enumerate all later gaps.
Suggested follow-ons: e37 for the exact branch spelling, a separately scoped
validated indirect-dispatch/jump-table unit, e38 LDDQU, e40 DF controls,
e16 hints/fences, and reviewed e39 composition before e06/e07 regeneration.
Semantic instruction lemmas and per-function return/copy/frame proofs remain
separate proof units. No blocker remains for this bounded legacy PALIGNR subset.

## Ancestry and local-only handoff

Pinned origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing reference: `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` (not imported).
Prepared clean HEAD: e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Successful empty read-only fork-name check preceded renaming only the prepared
`t3/x86-copy-shuffles` branch. The first sandboxed rename failed on read-only
shared Git metadata; its authorized retry succeeded and fast-forwarded only the
exact assigned `bcdd924bec65111aeb9244de21e5dba6286da845` checkpoint.
`fork-name-check.txt` and final successful network-repeat log preserve this.

`allowed-prerequisites.txt` records the exact eight-commit union of base..assigned
prerequisite history **before integration**. Only those plus scoped linear e34
implementation/evidence commits are allowed. `ancestry-before.txt`,
`ancestry-imported.txt`, and final audit/stat logs record merge-base,
`git log --oneline origin/llm_generated_proofs..HEAD` and diff stats.
No fork branch, active-unit history, e39, shell-created worktree or other branch
change was used. Shared plan/status were not edited.

No pushes, PRs, comments, reviewer requests, remote merges or branch deletions.
Future publication requires Charles's approval and would be
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.
The final SHA is in the handoff (a commit cannot include its own hash).
