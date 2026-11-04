# e29-arm-scalar-bitforms

Engineering complete for the deliberately small scalar kit. Two new complete
machine maps are available; three target functions remain partial at CCMP.
No function-correctness proof was attempted. No hardware/lifter refinement,
termination, all-input function behavior, or ABI/frame theorem is claimed.

Branch: `llm-proofs/e29-arm-scalar-bitforms`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ea3464df`.
Parent pin: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing pin (not imported): `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
Prepared HEAD: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Accepted prerequisite: `9ae8e6800fa044797efd98372857e6ac89b18e1b`.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No dependencies were installed. The e02 runtime/debug/JDK/Ghidra/venv and
shared Rocq wrapper were used read-only. Every mutable Ghidra project, cache,
configuration and output is under
`/home/charles/code/friends/.toolchains/e29-arm-scalar-bitforms`.
Java heap was bounded to 1 GiB. Proof builds/queries used virtual-memory cap
2000000 KiB, stack 65536 KiB and Dune `-j1`, without raising the limits.
There were no remote writes, pushes, PRs, comments, other-branch changes,
installations, subagents, shared campaign edits or host-wide process kills.

## Implementation and primary evidence

`ScalarLifter.check_bitform` checks both the instruction word and its complete
raw-pcode DAG before the existing scalar translator lowers it. Matching includes
operation order/arity, constants, register reads/writes, widths, and unique-node
dataflow. Unique addresses are canonicalized; overlapping or uninitialized
uniques still fail the existing independent checks. A pcode suffix, missing
write, altered flag operation, wrong mask or wrong instruction bytes fails.

The covered forms use ordinary X0..X30 operands:

- REV W/X: full 32/64-bit byte reversal, not REV16/REV32 or vector reversal.
- UBFIZ W/X: wrapping UBFM alias with `0 <= imms < immr < datasize`;
  `lsb = datasize - immr`, `width = imms + 1`. The actual rotation/mask
  pcode is retained, including both masks and explicit W-to-X zero extension.
- ORN W/X with LSL #0: width-bounded complement followed by OR; flags preserved.
- BICS W/X with LSL #0: AND with the width-bounded complement; N/Z from the
  width-specific result, C/V cleared. SLEIGH's temporary flag writes remain.

Zero-register operands and shifted ORN/BICS are deliberately rejected by this
new gate. No CCMP, SIMD, TLS, prefetch/hints, ZVA, SVE, MTE or callee support
was added. Existing ISA semantics, proofs and historical generated programs
were not changed. The supervisor and headless translator remain unchanged.

The complete e08 diagnostics were read at
`notes/e08-arm-lifts/logs/baseline01/{inet_makeaddr,rand_r,__memchr_nosimd,strcmp,__strlen_asimd}.ghidra.log`.
Fresh raw pcode comes from exact Ubuntu ARM64 glibc **2.35-0ubuntu3.15**,
SHA256 `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`,
Ghidra **11.4.2**, language `AARCH64:LE:64:v8A`, image base `0x100000`.
Existing e02 archive and runtime/debug pins are verified by the supervisor.
`scalar_bitforms/RAW.json` retains complete five-target traces plus 14 explicit
instruction-encoding fixtures. Every target instruction is checked against
runtime ELF bytes; generated .v/.pcode.json/.manifest.json files are separate
e29 artifacts. `HASHES.json` covers all new artifacts except itself.

Primary reference: [Arm A64 ISA, pseudocode v2020-12](https://documentation-service.arm.com/static/6023d61995978b529036da45),
reviewed BICS pp.61–62, ORN pp.350–351, REV pp.376–377 and UBFIZ/UBFM pp.556–559.
The binary encoding fields and scalar operations were checked against these
pages. UBFIZ inserts low source bits at the encoded position and zeros the
remaining destination bits; REV reverses bytes at the selected scalar width.
ORN preserves NZCV; BICS derives N/Z and clears C/V. `arm-reference.json`
records the exact manual hash, extraction commands and successful exits.
No copyrighted manual pages are committed.

## Actual target coverage and follow-on work

| Symbol | Model entry | Result |
|---|---|---|
| inet_makeaddr | `0x1f9d40` | Complete 19-instruction closed map, 76-byte extent |
| rand_r | `0x13e280` | Complete 15-instruction closed map, 60-byte extent |
| __memchr_nosimd | `0x19c7c0` | Strict failure at `0x19c81c`: `ccmp x6,x8,#0x0,mi` |
| strcmp | `0x192f80` | Strict failure at `0x192fb4`: `ccmp x2,x3,#0x0,eq` |
| __strlen_asimd | `0x19c940` | Strict failure at `0x19c970`: `ccmp x5,#0x0,#0x0,eq` |

`TARGETS.json` and full Ghidra logs retain the diagnostics. Failed scopes have
no accepted output directory or staging residue. The full raw traces retain
later instructions as evidence, without publishing an incomplete machine map.
First failures are not exhaustive missing-operation inventories. e30 should
consume the three exact CCMP frontiers and run the entire extent again;
`__strlen_asimd` also has later vector instructions and needs its separate
NEON gate. Astra proof units can later consume reviewed inet_makeaddr/rand_r
artifacts with real functional, memory and ABI/frame contracts. Such proofs
remain separate work; finite-map closure retains RETURN as caller boundary.

## Verification commands and results

All commands ran from the worktree root. Numbered logs contain exact command
arguments, output and real exit codes. The following final checks all exit 0:

- `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_bitforms.py`
  (log28): 25 exact-byte shapes, 12,800 independent formula/IL register and flag
  snapshots, 1,549 malformed/unknown/byte-mismatched pcode rejections, plus
  explicit unsupported encoding forms. Cases include both widths, same-register
  source/destination, zero/all-one/sign-bit inputs, random inputs, all initial
  NZCV combinations and dirty upper X bits for W writes.
- `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_bitforms.py --generate`
  (log16): 25 separate IL fixture statements, fixture typing theorem, and 150
  finite execution checks using Picinae's existing functional interpreter.
  This checks final X0..X30, SP/PC and all modeled flags for concrete states;
  it is not target CPU execution or a universal instruction-soundness proof.
- `/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'export PROOF_MEMORY_KB=2000000; ulimit -v 2000000; ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short @all'`
  (log20): full clean selective Dune build, including every new full .vo,
  all eight e11 fixtures, all fifteen e08 artifacts and existing smoke/core.
  No Dune verification is pending.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e29-arm-scalar-bitforms/validate.py --run validate01`
  (log13): fresh five-target extraction, all 23 e08/e11 reference programs and
  traces checked against fresh Ghidra output, receipt/record field comparisons,
  original seven strict-publication cases with private-state routing, the
  original unsupported-op subprocess, and a new mixed-new-form/CCMP failure.
  The expected failing driver scopes exit 1; the validating suite exits 0.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e29-arm-scalar-bitforms/replay.py --run targets02 --collect`
  (log21): final e29-only artifact collection after deleting an unused harness
  line. Programs/traces are unchanged from log13; the e29 harness hash changes.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e29-arm-scalar-bitforms/replay.py --run targets03`
  (log24): fresh two-map .v/.pcode.json/.manifest.json replay is byte-identical;
  all three precise rejection diagnostics and atomic failures reproduce.
- `python3 notes/e29-arm-scalar-bitforms/collect.py --run raw07` (log25), then
  `cmp Examples/claude/lifter/scalar_bitforms/RAW.json /home/charles/code/friends/.toolchains/e29-arm-scalar-bitforms/raw07/raw.json`
  (log29): fresh raw target/encoding fixture evidence reproduces exactly.
- `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_scalar.py`
  (log18): all ten original translator tests pass.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/check-harness.py`
  (log19): original actual-map closure and four negative checks pass.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/check-artifacts.py`
  (log23): unchanged e08 hashes, naming adapters, ELF bytes, closure and data
  evidence pass. No historical receipts were rewritten.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e29-arm-scalar-bitforms/recheck-historical.py /home/charles/code/friends/.toolchains/e29-arm-scalar-bitforms/validate01/reference-smoke`
  (log22): original e11 historical AST/finite-effect comparison against fresh
  Ghidra IL; all 69 instruction boundaries and 128 samples/instruction pass.
  Eighteen historical AST differences remain recorded in this unit's own
  `historical/` diffs; no universal equivalence claim is made.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e29-arm-scalar-bitforms/check-artifacts.py`
  (log26): new file hashes, exact ELF instruction bytes, emitted fixture IL,
  names, implementation hashes and complete map closure pass.
- `python3 tools/audit-proof-source.py --base 9ae8e6800fa044797efd98372857e6ac89b18e1b Examples/claude/lifter/scalar_bitforms`
  (log27): three new Rocq sources, no admission/axiom/parameter declarations.
- `python3 notes/e29-arm-scalar-bitforms/audit.py` (log30): exact ancestry
  boundary and 647 protected source/proof/reference-evidence hashes pass.

The existing e11 receipts intentionally identify the old implementation.
`REFERENCE-DELTAS.json` records the sole expected implementation field change:
`pcode2coq_scalar.py`. Programs, raw pcode and all other checked receipt fields
remain identical. The old implementation-pin-only checker cannot certify an
explicit extension as receipt-identical; it was not changed or misreported.

Development failures are retained honestly: early collection attempts fixed
a reserved Ghidra field name, unnamed vector varnodes in evidence collection,
the JPype byte-array API, disassembly-ahead writes and LSL-preferred encodings.
Initial finite-fixture builds fixed the interpreter argument order and optional
type constructor. Log06/07 caught the oracle reading an irrelevant immediate
as a register and the guard's signed Java representation of 64-bit constants.
Final successful checks above supersede those attempts. No partial theorem or
admission was committed.

## Assumptions and provenance boundary

`/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash notes/e29-arm-scalar-bitforms/print-assumptions.sh`
(log31) exits 0, independently querying all four new facts. Verbatim output for
`e29_bitforms.finite_execution`:

```text
Closed under the global context
```

Each of `e29_bitforms.welltyped`, `e29_inet_makeaddr_arm8.welltyped` and
`e29_rand_r_arm8.welltyped` has exactly this inherited output:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This dependency comes from existing Picinae/Stdlib typing automation. No new
assumption declaration was introduced. Binary extraction assumptions: N/A.
Function-correctness assumptions: N/A; there is no such theorem in this unit.

## Ancestry and publication audit

The successful read-only collision check was
`git ls-remote --heads fork refs/heads/llm-proofs/e29-arm-scalar-bitforms`,
exit 0, empty output. The sandbox's first DNS attempt failed, so that same
read-only command was retried with reviewed network access. Only the prepared
local branch was renamed, then `git merge --ff-only 9ae8e6800fa044797efd98372857e6ac89b18e1b`
succeeded. Git metadata writes required sandbox escalation because linked
worktree metadata lives outside the workspace; no new worktree was created.

The five allowed commits above the pinned origin base are exactly:

```text
71470bffba65392adf1873a3df9f0cf0ca4f1ac9 e00
081d0233cd6667803b3907343b2fea6dc9eba714 e02 implementation
052521a753adbda077843ec7b259801282a7b1e9 e11 reviewed e02 import
378fe1b57514b9af3f017a72b4ca665910156cc7 e11 implementation
9ae8e6800fa044797efd98372857e6ac89b18e1b e08
```

Only this unit's local commit follows e08. `ancestry-before.txt` records the
imported merge-base/log/stat; `ancestry-staged.txt` records the final staged
scope. The post-commit full SHA, merge-base, complete log/stat and clean status
are recorded in the unit's external final audit under
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/e29-arm-scalar-bitforms/`.
Future PRs require Charles's approval and would use
`CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs`.
