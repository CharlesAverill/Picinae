# e30-arm-ccmp

Engineering implementation of precise CCMP register/immediate lowering, with
three new complete scalar maps. No function correctness, hardware refinement,
termination, or ABI/frame theorem is claimed. Seven target maps remain blocked
at the exact frontiers below and are not published, even partially.

Branch: `llm-proofs/e30-arm-ccmp`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-4b9d096d`.
Origin pin: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing pin (not imported): `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
Prepared HEAD: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Accepted e29 prerequisite: `9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b`.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No installation occurred. e02's exact pinned runtime/debug ELF, Ghidra 11.4.2,
JDK and Python venv were reused read-only; mutable Ghidra projects, cache,
configuration and extraction outputs are private under
`/home/charles/code/friends/.toolchains/e30-arm-ccmp`.
The shared Rocq wrapper was verified as Rocq 9.1.1 / OCaml 4.14.2 / Dune
3.22.2 (log17) and reused read-only. Every Dune/Rocq/query process is bounded
to 2000000 KiB virtual memory, stack 65536 KiB, and Dune `-j1`. Java heap is
at most 1 GiB. There were no limit increases, host-wide kills, subagents,
worktree creations, remote mutations, pushes, PRs, comments, shared plan/status
edits, or changes to earlier generated programs/receipts.

## Implementation and semantic boundary

`ScalarLifter.conditional_compare` recognizes the instruction word and exact
Ghidra 11.4.2 raw-pcode DAG, including opcode/order/arity, widths, constants,
architectural register slices, canonical unique-node dataflow, all fallback
writes, the saved old condition and a CBRANCH to precisely `instruction+4`.
Both immediate/register forms, both W/X widths, X0..X30 and WZR/XZR source
positions, all sixteen condition encodings (AL and NV always true), all imm5
values 0..31 and fallback NZCV values 0..15 are covered. Reserved encoding bits
remain checked. A same-name instruction with mismatched bytes/pcode rejects.
Unique initialization and overlapping-range checks remain active.

Actual SLEIGH pcode saves the old condition, writes the fallback flags, then
branches to the next instruction if the saved condition is false. The compare
suffix otherwise computes subtraction N/Z, unsigned no-borrow C and signed
overflow V. Generic machine CBRANCH translation rejects trailing pcode; CCMP
has this deliberately narrow, separately validated suffix lowering:
`prefix; If(skip) Nop compare_suffix`. The jump to the next instruction becomes
natural fallthrough. No general CFG handling is relaxed, no new whitelisting
of internal loops or arbitrary suffixes occurs, and other instruction gates
are unchanged. TEMP scratch flags preserve their previous values on fallback;
all four are updated on comparison. The architectural and scratch flags are
modeled 8-bit cells; normalized architectural NZCV inputs are 0 or 1, as in
SLEIGH's boolean-flag convention. W compares read low 32 bits without writing
or clearing any X register. All GPR/SP/PC cells are preserved by CCMP itself.

Primary semantics: [Arm A64 ISA / pseudocode v2020-12](https://documentation-service.arm.com/static/6023d61995978b529036da45),
CCMP immediate/register pages 87/88 and shared `ConditionHolds` pseudocode.
`arm-reference.json` records the exact PDF SHA256 and reviewed locations. The
web fetch timed out; the previously pinned official PDF/text was read locally
without modification. The operation is width-specific subtract-with-flags
when the condition holds and all four encoded NZCV bits otherwise. Instruction
soundness over all states, timing/DIT, exceptions and function behavior remain
separate proof work. No new NEON/TLS/SVE/ZVA/MTE/PRFM/callee support was added.

## Exact target results and follow-on units

Exact source: Ubuntu ARM64 glibc **2.35-0ubuntu3.15**, libc SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`,
Ghidra **11.4.2**, `AARCH64:LE:64:v8A`, model image base `0x100000`.
The unchanged supervisor checks runtime/debug and dependency archive pins.
`RAW.json` contains all instructions from all ten target extents, with actual
encoding fixtures gathered by pinned Ghidra rather than invented pcode.
Every target instruction is checked against runtime ELF bytes. Only complete
maps with closed direct edges/fallthroughs are adapted to distinct e30 names;
RETURN remains a caller ABI boundary. Manifests record ELF bytes, closure,
data requirements, implementation hashes and the naming-only substitution.

| Target | Entry | Result / precise next frontier |
|---|---|---|
| __memchr_nosimd | 0x19c7c0 | Complete, 56 instructions / 224 bytes |
| strcmp | 0x192f80 | Complete, 77 instructions / 308 bytes |
| wcschrnul | 0x19e4c0 | Complete, 9 instructions / 36 bytes |
| __strlen_asimd | 0x19c940 | Reject at 0x19c9e0: `ldp q1,q2,[x1,#0x20]!`, q1/z1 unmodeled |
| memcmp | 0x194640 | Reject at 0x1946e4: `cneg w0,w0,cc` |
| sigandset | 0x13b4d0 | Reject at 0x13b504: `mrs x2,tpidr_el0` |
| sigorset | 0x13b520 | Reject at 0x13b554: `mrs x2,tpidr_el0` |
| sigaddset | 0x13b2b0 | Reject at 0x13b2f4: `mrs x2,tpidr_el0` |
| sigdelset | 0x13b310 | Reject at 0x13b354: `mrs x2,tpidr_el0` |
| sigismember | 0x13b370 | Reject at 0x13b388: `mrs x2,tpidr_el0` |

`TARGETS.json` and full Ghidra logs retain exact raw rejection diagnostics.
Failed target output directories and staging residue are absent. Complete
maps replay byte-for-byte; first rejections are not exhaustive missing-feature
inventories. Follow on with a-neon-lemmas / the explicit ARM vector lowering
unit for __strlen_asimd, a small guarded CNEG alias unit for memcmp, and e09
TLS support for signal helpers. Later approved proof units may consume the
three reviewed maps for functional specifications, inhabited domains and
ABI/memory frames; none of those properties follows from typing/finite tests.

## Validation and honest development failures

Every numbered command log contains exact argv, CWD and actual exit status.
The final successful checks include:

- log05: `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_ccmp.py`,
  exit 0: 339 actual encoding/pcode shapes, 81360 independent A64-formula/IL
  snapshots and 65336 malformed encoding/DAG/branch/arity/width/output
  rejections. Covers all conditions and old flags, every immediate/fallback,
  same/zero operands, dirty upper X bits, unsigned carry, signed-overflow edges
  and dirty scratch bytes on both paths. All architectural cells are compared.
- log19: the same script with `--generate`, exit 0: 339 fixture statements,
  1574 checks against the existing Picinae functional interpreter in thirteen
  finite-execution facts, plus fixture typing. Every condition/form/width has
  every old-NZCV input; additional actual shapes include both extreme old flags.
  Interpreter continuations are resumed with bounded fuel; exhaustion fails.
- log03: `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e30-arm-ccmp/validate.py --run validate01`,
  exit 0: all ten fresh exact-ELF targets; fresh replay of 15 e08, eight e11
  and two e29 artifacts, unchanged program/pcode/record content; eight mixed
  atomic-publication failure batches and unsupported-op subprocess. Expected
  failing driver invocations exit 1; the suite exits 0. `REFERENCE-DELTAS.json`
  records solely expected translator implementation-hash changes; no old
  receipt is rewritten or asserted identical to an extended implementation.
- log11: `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e30-arm-ccmp/replay.py --run replay01`,
  exit 0: independent fresh three-map .v/.pcode/.manifest deterministic replay,
  exact seven frontiers, no accepted output or staging after failure.
- log10: `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e30-arm-ccmp/check-atomic.py`,
  exit 0: five malformed-pcode subprocess exits 1 with no output; deterministic
  unique renumbering and rejection of overlapping unique ranges.
- logs08/09: unchanged `test_scalar.py` (ten tests) and `test_bitforms.py`
  (12800 snapshots,1549 rejections), exit 0.
- log12: historical comparison against fresh e11 smoke, exit 0: 69 instruction
  boundaries and 128 samples per instruction. Eighteen known historical AST
  differences are retained in this unit's `historical/`; old programs/diffs
  remain unchanged. Finite comparisons are not universal equivalence.
- logs13/14: original e08 closure negatives and all artifact/hash/byte/data
  checks, exit 0. log22: new artifacts, raw ELF bytes, fixture IL, naming,
  implementation hashes, and closed machine maps, exit 0.
- logs21/23: fresh raw fixture/target collection and byte-for-byte comparison,
  exit 0.
- logs15/16 and24/25: new Rocq source audit and exact ancestry plus 897 protected
  historical/core/proof/e02/e08/e11/e29 source/evidence hashes, exit 0.

The initial collection guard development exposed SLEIGH's condition-before-
zero-source ordering and distinct XZR-vs-WZR expansion; those were corrected
before the logged target extraction and finite tests. Initial Dune log07
failed the finite fixture because the inherited straight-line harness did not
resume `FIStmt` at If. Log18 is an invalid debug filename rejection (exit 1).
The final fixture runner uses explicit bounded continuation execution; no
admission, axiom or unproved function lemma was added. Log20 stalled before any compiler started in the sandbox and was ended with
exit130 by signaling only its verified e30 Dune PID. Log26 reruns with the
same limits outside the sandbox. No success is claimed for the failed or
interrupted development checks.

## Final full build and assumptions

Final full selective Dune verification (log26), exit **0**:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'export PROOF_MEMORY_KB=2000000; ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short @all'
```

The initial full build compiled every existing selected dependency and all
three new map .vo files; after the fixture-harness correction, this successful
@all run kernel-checked the final fixture and all full targets. No Dune
verification is pending. No .vos-only shortcut or imported admission is used
as evidence for a new fact.

Explicit queries (log30), exit **0**:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash notes/e30-arm-ccmp/print-assumptions.sh
```

All seventeen new facts were queried against final .vo files. Each of
`e30_ccmp.finite_execution_0` through `e30_ccmp.finite_execution_12` prints
verbatim:

```text
Closed under the global context
```

Each of `e30_ccmp.welltyped`, `e30___memchr_nosimd_arm8.welltyped`,
`e30_strcmp_arm8.welltyped`, and `e30_wcschrnul_arm8.welltyped` prints
verbatim:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited typing-automation dependency from existing Picinae and
Stdlib, with the same provenance as e11/e08/e29. No new assumption declaration
was introduced. Binary extraction assumptions: N/A. Instruction-universal and
function-correctness assumptions: N/A, because no such theorem is introduced.

## Ancestry and publication

Read-only `git ls-remote --heads fork refs/heads/llm-proofs/e30-arm-ccmp`
returned exit 0 and empty output (after the sandbox DNS attempt failed).
HEAD was the prepared e00 commit; its ancestor relationship to accepted e29
was checked before renaming only the prepared branch. Metadata writes needed
sandbox escalation because linked-worktree Git metadata is outside the writable
checkout. `git branch -m llm-proofs/e30-arm-ccmp`, followed by
`git merge --ff-only 9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b`, succeeded.
No fork history was used as a base. The complete permitted history above origin
is exactly:

```
71470bffba65392adf1873a3df9f0cf0ca4f1ac9 e00
081d0233cd6667803b3907343b2fea6dc9eba714 e02
052521a753adbda077843ec7b259801282a7b1e9 e11 reviewed e02 import
378fe1b57514b9af3f017a72b4ca665910156cc7 e11
9ae8e6800fa044797efd98372857e6ac89b18e1b e08
9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b e29
```

The final staged whitespace check excludes verbatim Ghidra command logs and
historical unified diffs: those intentionally preserve upstream trailing
whitespace / diff-context indentation. The initial all-file staging check
rejected only that raw evidence and made no commit; log33 checks source and
other artifacts without rewriting the evidence.

Only e30's local commit follows those prerequisites. Log01 records merge-base,
log and diff stat before implementation; the final staged and external
post-commit audits record the same after implementation. The full own commit
SHA and final clean status live under this unit's external evidence directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/e30-arm-ccmp/`.
Future publication requires Charles approval and would be
`CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs`.
Only a-div/a-ldiv currently have publication approval.
