# e11 canonical scalar lifter — completed within the explicit scalar boundary

This unit implements a new, versioned **strict AArch64 scalar replacement**
against Ghidra 11.4.2 raw SLEIGH pcode and this repository's Picinae model.
It does not recover the unavailable historical `b7f0122` plus uncommitted
`claude/amd64-fixes` checkout. The old library and drivers remain unchanged;
the supported campaign entrypoint is `tools/ghidra-lifter/lift-scalar.py`.
No new function correctness proof or semantic-kit lemma was attempted.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

## Provenance and lineage

Worktree: `/home/charles/.t3/worktrees/Picinae/t3-4aebc652`.
Branch: `llm-proofs/e11-canonical-lifter`.
Prepared HEAD was reviewed e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Pinned origin and merge-base:
`49956416928e5b6bb3928b54ae33e3b81091f006`.
The sole imported candidate is e02
`081d0233cd6667803b3907343b2fea6dc9eba714`, merged locally as reviewed **partial
evidence**, not a completed pipeline prerequisite. No e03/e04, fork history,
or timing history was imported. The timing reference remains contextual only:
`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
Before/imported/after ancestry and diff statistics are saved beside this file.
The required exact read-only fork-name check returned empty before renaming
only the prepared local branch. There was no push, PR, remote comment, remote
mutation, worktree creation, or edit to shared plan/status files.

The reviewed e02 README, compatibility probe log, provenance, restricted smoke
adapter, library implementation and historical lifts were read. The original
probe's missing `LiftInfo.prependProgName` is a real symptom, but filling that
attribute alone would retain incorrect BOOL_NEGATE, LZCOUNT, partial-register,
static-memory and temporary behavior. The replacement avoids that incompatible
LiftInfo/typctx API instead of presenting it as recovered historical code.

All dependency material is reused read-only from
`/home/charles/code/friends/.toolchains/e02-arm-inventory`: exact ARM runtime,
debug ELF, patched Ubuntu source, Ghidra, JDK and Python venv. No dependency
was installed and no shared environment/project was changed. The supervisor
verifies **every archive in e02's artifacts.lock.json** plus runtime/debug
hashes on each invocation. Ghidra's actual runtime version is checked as 11.4.2.

- Runtime: Ubuntu ARM64 glibc **2.35-0ubuntu3.15**,
  SHA256 `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
- Debug ELF SHA256:
  `c95b2118b5ea5ed12db5c745fb95af4dd696ce07d3ce966a60124519a443e9e7`.
- Build ID: `977c021c364ee3c495c0e5f2375bf6ba2124a6da`.
- Ghidra release archive SHA256:
  `795a02076af16257bd6f3f4736c4fc152ce9ff1f95df35cd47e2adc086e037a6`.
- Temurin JDK 21.0.8+9, Python 3.12.9 / PyGhidra 2.2.1 / JPype1 1.6.0 /
  packaging 25.0; unchanged e02 lock pins dependencies.
- Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2 verified in log 23.

Actual replacement source hashes are in `implementation.sha256` and both
fixture `SUCCESS.json` manifests. Those manifests also record function bytes,
ELF/Ghidra entries, output hashes and selected symbol extents. Each instruction
has the actual bytes, assembly and raw pcode in the adjacent `.pcode.json`.

All mutable Java home, preferences, config, cache, projects, temporary files,
logs and extraction scratch/output stay in the private
`/home/charles/code/friends/.toolchains/e11-canonical-lifter` tree. Projects are
fresh imports with autoanalysis disabled and are deleted after each run.
Java heap is **-Xmx1G**, with inherited Java/Python injection options cleared;
a private file lock enforces one Java invocation at a time. No target binary
was executed. The Python tests interpret small IL fragments, not target code.
Archival evidence is in this unit's repository notes; no external campaign
evidence directory or shared campaign file was modified.

## Replacement behavior and boundaries

`pcode2coq_scalar.py` is a pure Python strict translator with a separate
Ghidra adapter and supervising CLI. It accepts only AARCH64:LE:64:v8A.
Supported scalar registers are X0–X30, SP, PC, and the model's eight byte
condition/temporary flags. Exact register slices use Ghidra's base register
and byte offset; writes merge the addressed slice. W-to-X zero extension
comes from explicit raw SLEIGH ZEXT/base writes, not an invented rule for every
partial write. Unsupported registers (including vector, TLS and system state)
raise errors. Reads/writes of ordinary RAM remain explicit Load/Store terms;
addresses are 64-bit, LittleE, with exact pcode access size. Data constants and
references retain absolute Ghidra addresses (ELF + 0x100000).

Each instruction resets the unique map and initialization set. Unique storage
is numbered deterministically by first encounter of inputs then output in raw
pcode order, starting at V_TEMP 0. Overlapping differently sized unique ranges
and reads without a definition on every reachable path are rejected. No temp
state is inherited from a preceding instruction. Scalar raw operations cover
COPY, integer/boolean arithmetic and comparisons, casts, piece/subpiece,
carry/signed overflow, POPCOUNT/LZCOUNT, RAM LOAD/STORE and supported flow.
BOOL_NEGATE is xor **1**, not bitwise NOT. LZCOUNT is width minus Picinae's
OP_BITWIDTH (N.size), including CLZ(0)=width. Large shift counts are tested
before count truncation. Unknown opcodes are checked even in pcode that an
unconditional internal branch would skip.

Forward intra-instruction constant branches become structured If/sequence
terms, with definite temporary initialization at joins. Backward/internal
loops, malformed/out-of-region flow, indirect calls and unsupported trailing
machine-branch pcode are rejected. Direct calls are accepted only with global
addressing; the caller and explicitly selected callees are combined into each
global program. Absolute return-address pcode is preserved. Direct machine
edges must close over the selected extents. Returns and indirect branches
remain explicit jumps; there is no total-control-flow or termination theorem.
Only the actual A64 NOP encoding `1f2003d5` may yield an empty Nop instruction;
unsupported instructions/userops never become Nop or zero. Other Nops are
structured control-flow empty branches.

The instruction allowlist and per-op/register checks are deliberately stricter
than all scalar A64. In particular CCMP, system/TLS, NEON, SVE, ZVA, MTE,
BTI/hints, barriers, floating point and atomic/exclusive semantics are not
implemented. Such functions are rejected, not partially published. No x86
lifting coverage is claimed. Later units can reuse the supervised publication
pattern, but must implement and validate their own architectural support.

Static memory theorem generation is absent (`staticMemory=False` throughout).
There are no generated static-memory axioms or hidden memory-value hypotheses.
The ffs lookup table remains an ordinary load from input memory and needs a
separate content/functional proof in the proof unit.

A fresh per-run nonce receipt is written only after **all** symbols succeed.
The supervisor checks the launcher exit, receipt nonce, complete requested
symbol list, generated output hashes and exact output file set, then atomically
renames a sibling staging directory. On failure it removes staging and returns
1 even when Ghidra returns 0; the actual Ghidra diagnostic is preserved. Existing
output directories are rejected rather than treated as fresh success. Extraction
publication is not a substitute for the subsequent Dune kernel check.

## Actual checks and exact historical differences

All commands and real exit codes are captured in numbered logs. Earlier failed
attempts remain visible; no failure is relabeled as success.

| Check | Recorded command/log | Actual exit |
|---|---|---|
| Fresh final six-symbol extraction + global call extraction + capped Dune build | `bash notes/e11-canonical-lifter/reproduce.sh verified` (18) | 0 |
| Clean full-vo build, eight fixtures | read-only Picinae wrapper; `ulimit -v 3000000; ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short @scalar-lifter` (15) | 0 |
| Ten strict translation/arithmetic regression tests | `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_scalar.py` (17) | 0 |
| Seven failing symbol/call/instruction batches and unsupported CALLOTHER subprocess | `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e11-canonical-lifter/check-failures.py` (16) | harness 0; each expected failure 1 |
| All eight Print Assumptions queries | read-only Picinae wrapper, `bash notes/e11-canonical-lifter/print-assumptions.sh` (19) | 0 |
| Fixture hashes, instruction counts, selected object audit | `python3 notes/e11-canonical-lifter/check-artifacts.py` (20) | 0 |
| Added Rocq source admission/axiom audit | `python3 tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006 Examples/claude/lifter/scalar_smoke Examples/claude/lifter/scalar_global` (21) | 0 |
| Per-instruction historical comparison | `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e11-canonical-lifter/compare-il.py` (11) | 0 |
| Fresh-project byte determinism | logs 14 and 22 | 0 |

The clean build began without Dune outputs; all eight fixtures have actual full
`.vo` files. The explicit Dune module list selects no e02 inventory evidence
`.v` duplicate. Historical generated lifts/proofs were not edited. The global
fixtures each contain the same 108-instruction combined program: the 9-instruction
mempcpy wrapper plus 99-instruction generic scalar memcpy. At Ghidra 0x194a60,
BL writes X30 = 0x194a60 + 4 and jumps to the included 0x19ab40 body. This is
call-address/typing evidence, not a memcpy/mempcpy correctness result.

The regression tests exhaust all 65,536 byte input pairs for unsigned carry,
signed-add overflow and signed-subtract overflow; check zero/basis/random CLZ
inputs at 8/32/64 bits; test BOOL_NEGATE, all fitting byte/halfword/word slices,
W zero-extension, wide shift counts, RAM effects, forward branch paths, call
addressing and strict unknown op/register/instruction/internal-loop rejection.
Fresh-project final replay produces byte-identical `.v` and raw-pcode JSON for
all six leaf fixtures and both global fixtures (16 files total).

Compared with historical generated IL, all **69 instruction slots** and their
bytes/assembly agree. Normalized parsed IL syntax is identical at 51 slots.
Exact full unified diffs (`<symbol>.diff`) retain every change, including
format/header differences. The 18 structural IL differences are:

| Symbol | Relative offsets | Explanation |
|---|---|---|
| toascii | none | identical parsed IL at both instructions |
| div | 0x8 | factor the common X3 write after the conditional SDIV result |
| ldiv | 0x4 | same factoring for X0 |
| swab | 0x4, 0x10 | signed overflow uses the sign-bit identity, widened from one bit |
| ffs | 0xc, 0x14, 0x20, 0x30, 0x3c, 0x50 | same overflow identity; 0x14 also retains the raw constant temp rather than substituting it |
| ffs | 0x48, 0x5c | SUBPIECE becomes exact Extract instead of shift + low cast |
| ffsl | 0x10, 0x1c, 0x34, 0x40 | same overflow identity; 0x1c also retains the raw constant temp |
| ffsl | 0x24, 0x3c | factor the common X0 write after the conditional increment |

`comparison.json` records every differing address. An independent small IL
parser/evaluator checked architectural registers, memory updates and jump
results for **128 samples at each of the 69 instructions** (8,832 instruction
comparisons), with zero/all-one inputs and deterministic random inputs.
Temporaries are intentionally excluded from the architectural comparison.
These finite tests support review; they are not an equivalence proof or a
binary functional correctness proof. ffsl/ffsll remain one aliased body, not
separate implementations.

Initial failures: the first allowlist omitted scalar RBIT even though its raw
pcode was supported; the complete batch was discarded despite launcher exit 0.
A first negative test mistakenly used __memcpy_generic as a NEON body. Actual
bytes/pcode show it is scalar and it was correctly accepted; the corrected
negative uses __memcpy_simd and rejects q0/base z0. The e02 plan prose's generic
memcpy NEON characterization must not override this byte evidence. That
unselected diagnostic output stays only in private extraction scratch.
The sigaddset batch rejects CCMP before reaching TLS; memset_generic rejects
DUP before reaching ZVA; strlen_mte rejects LD1 before any MTE-specific effect.
Thus those are **family rejection tests**, not claims to have reached each
system feature. Explicit MRS/DC/SVE/BTI tests and the allowlist also reject
those unsupported operations. All full Ghidra logs are archived under logs/ghidra.

## Assumptions and handoff

All eight new typing theorems finish with `Qed`; verbatim per-module output
is log 19, also printed during the clean build. Each has exactly the existing
core/Stdlib dependency:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is inherited through the existing Picinae typing automation, not a new
declaration. There are no new Admitted/admit/Axiom/Parameter declarations and
no imported admitted dependency in the queried typing theorems. Binary-only
assumptions are N/A; typing assumptions are reported above.

To reproduce, choose a new output run name and run `bash
notes/e11-canonical-lifter/reproduce.sh NEW_RUN_NAME`, then the test, comparison,
artifact-check, source-audit and assumptions commands above. No bootstrap or
installation is needed. Dune final verification is complete, not pending.

There is no blocker within the validated scalar subset. Historical exact
recovery remains unavailable and full A64 coverage is outside this unit.
Follow-on engineering: e08 can use this strict scalar frontend for individually
selected, validated functions; e09/e10/e12/e13/e14 must add TLS/NEON/ZVA/SVE/MTE
support with explicit semantics. CCMP and other rejected scalar shapes need
separate reviewed frontend work before broader signal helper extraction.
Proof units retain ownership of function contracts, static-data correctness,
ABI/frame theorems, termination and semantic-kit lemmas. Existing div/ldiv
proof work can continue on historical unchanged lifts independently.

Only e00, partial e02, this unit's local import merge and its own implementation
commit(s) are permitted above the pinned origin. The full final commit SHA is
reported in the handoff rather than embedded self-referentially here.

Whitespace verification: source, fixtures and notes pass the staged check in
log 26. Verbatim unified diffs contain diff-context space-before-tab sequences,
and Ghidra's raw application logs contain trailing spaces; these evidence-only
files are excluded from whitespace lint to preserve the exact original text.
A whole staged whitespace check flagged those evidence bytes (exit 2), not
source defects. Final full-SHA ancestry and after-stat evidence are exported
after the local commit to the authorized unit-specific external evidence path
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/e11-canonical-lifter/final-audit.txt`.
