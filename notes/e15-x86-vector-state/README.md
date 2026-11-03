# e15: coherent AMD64 wide-vector state

Engineering prerequisite for e17; no glibc function proof or semantic transfer
theorem is included. The implementation is in `Picinae_amd64_avx512.v`, under
the explicitly imported `AMD64_AVX512` namespace. `Picinae_amd64.v`, all its
existing contexts, lifts and proofs, and the common pcode2coq driver are unchanged.
The engineering unit is complete: the clean full Dune build exits 0, with
1,360,036 KiB maximum RSS and 2:13.75 elapsed time. No implementation blocker
remains within the state/metadata scope; instruction lowering remains e17 work.

## Environment rule (Charles, unchanged)

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No installation or environment mutation was needed. Rocq uses the read-only
wrapper above. Python checks use the existing e01 Python 3.12.3 venv read-only,
with `-B` to avoid bytecode writes. The implementation uses only the standard
library. Ghidra source files were read, without launching Java or changing e02.
The repository `Examples/claude/SKILL.md` was read for conventions; Charles's
no-admission, no-subagent and 2,000,000 KiB resource limits override its proof
workflow suggestions. No new function proof was attempted.

## Representation and compatibility boundary

There is one variable `R_ZMM r : 512 bits` per finite slot `Z0` through `Z31`.
XMM/YMM names are **views**, never separately stored variables:

| View | Expression | Stored cell |
| --- | --- | --- |
| XMMn | bits 127:0 | `R_ZMM Zn` |
| YMMn | bits 255:0 | `R_ZMM Zn` |
| ZMMn | bits 511:0 | `R_ZMM Zn` |
| Kn | bits 63:0 (or an explicitly selected low-width view) | `R_K Kn` |

K0 through K7 are all 64-bit data cells. EVEX.aaa=0 maps to absence of a
writemask, independently of K0's contents. All architectural register IDs are
finite constructors, so the IL cannot accidentally allocate ZMM32 or K8.
Temporaries retain the old arbitrary-N naming convention and inferred widths.
As in the existing architecture, typed stores must satisfy Picinae's `models`
predicate; the raw function type `store` alone does not bound stored integers.

The companion copies the old scalar declarations and their widths, including
the existing MXCSR model, and instantiates the same IL/theory/statics/automation/
interpreter/simplifier functors. It does not assert a complete x86 machine model.
Memory and page-permission definitions retain the old 64-bit little-endian
model. Scalar variables and IL syntax in the two architectures are different
types; importing an old generated program is not a conversion to the companion.
No old theorem is claimed to transfer. No projections that discard upper lanes
or masks, store embeddings, or general bridge/semantic lemmas are supplied.

`vector_read`, `xmm_write_preserve`, and `vector_write_zero_upper` build explicit
IL expressions/statements over the canonical cell. A replacement RHS must have
the selected view width: `Concat` lets the typechecker reject a mismatch rather
than introducing a truncating cast. Mask read/write builders similarly use
8/16/32/64-bit views of the full 64-bit cell. These builders are register
operations; they do not check opcode legality or select an instruction policy.
For example, the generic preserve builder can describe a pcode slice update to
a high register, but that does not make a legacy instruction address XMM16.

## Exact required operand inventory

Assigned prerequisite e01 commit:
`131ad4b86cf4abcbd392048297038f3f219423bb`. Runtime:
`/home/charles/code/friends/.toolchains/e01-x86-inventory/runtime/lib/x86_64-linux-gnu/libc.so.6`,
Ubuntu glibc **2.35-0ubuntu3.12**, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`. The runtime hash was
independently checked in `logs/13-primary-local-sources.log`.

`operand_inventory.py` pins e01's inventory and disassembly hashes and selects
the actual 20 AVX512/EVEX memcpy/memmove/mempcpy/chk extents. It verifies every
printed vector name against the layout and encoding reach. `copy-operands.json`
records each extent's names, address, size, hash, register views and instruction
shapes, with first-site bytes and counts. This does not close external branches
or turn symbol sizes into complete reachable implementations.

Observed views are XMM0–1, YMM0–3 and YMM16–31, and ZMM0–25 and ZMM28–29.
Together these require **all 32 canonical physical slots**, including their
upper halves when only a YMM view is used. There are 50 distinct named views.
The explicit vector instructions in these symbol extents are:

| Encoding / mnemonic | Count |
| --- | ---: |
| EVEX VMOVDQU64 | 218 |
| EVEX VMOVUPS | 128 |
| EVEX VMOVNTDQ | 44 |
| EVEX VMOVDQA64 | 32 |
| VEX VMOVDQU | 24 |

No explicit opmask operands occur here. The script checks both the disassembly
and the EVEX P2 z/aaa bits (all zero). The opmask bank implements the assigned
e15 state contract, not evidence that a masked copy path was found. Masked
strings and additional opcodes must be inventory-gated by e18. The metadata is
an operand handoff, not complete instruction coverage or lift correctness.

## Primary sources and requirements for e17

Local primary implementation source: **Ghidra 11.4.2 PUBLIC**, source revision
`0b61b34bb9c98108eefd9404f45446dae6a1c5eb`, under
`/home/charles/code/friends/.toolchains/e02-arm-inventory/ghidra_11.4.2_PUBLIC`.
`logs/13-primary-local-sources.log` saves version, source hashes, register
declarations and representative VEX/EVEX definitions. `ia.sinc` defines the
vector bank at byte offset 0x1200 with a 64-byte stride and the mask bank at
**decimal 2100**, with an 8-byte stride. Full XMM/YMM/ZMM views start at bit 0.
`ia.sinc:1594–1669` distinguishes merging/zeroing and the no-writemask selector;
`avx512.sinc:1331–1350` shows mask application followed by full ZMM zero extension.
These files contain opaque pcode userops: reading them is not a proof that those
operations have been lowered to Picinae.

Manual cross-check: Intel SDM **September 2016**, Volume 2B, order number
**253667-060US**, [official PDF](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf),
MOVDQU pp. 4-67–4-73 and MOVUPS pp. 4-130–4-132; Volume 2C,
**326018-060US**, [official PDF](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2c-manual.pdf),
VZEROUPPER p. 5-565. These versioned manuals were inspected online. The
following is a register-policy checklist for later lowering, not a blanket
statement for every instruction sharing an encoding:

- For these packed moves, legacy XMM destinations preserve bits 511:128;
  VEX.128/256 destinations clear bits above their active vector width.
- EVEX register destinations combine active elements with the old destination
  for merging or zero for zeroing, then clear bits above VL through bit 511.
  Element size and number of mask bits come from the opcode and VL.
- Masked stores preserve disabled memory elements; they do not read/write
  zero-filled substitutes. Masked-off loads require instruction-specific
  access suppression. e15 supplies no masked memory lowering.
- Writemask selector zero denotes unmasked operation. K0 remains usable as
  ordinary mask data. Reject zeroing with selector zero or memory destination;
  validate any further opcode restrictions before using the helper metadata.
- VZEROUPPER's local Ghidra long-mode definition clears bits 511:128 of slots
  0–15 and does not write slots 16–31. It is a separate instruction policy,
  not the generic effect of reading a YMM view. It is absent from these 20
  wide-copy symbol extents.
- Slice writes from pcode must merge into the canonical cell, and subsequent
  explicit zero-extension must update that same cell. Preserve original source
  values when destination/source alias or temporaries span multiple updates.
- Memory stores do not clear the source vector's upper lanes. High registers,
  full 512-bit values and high mask bits must never be mapped to zero or cut
  down to the baseline YMM context.

`tools/amd64_vector_layout.py` provides strict names/widths, little-endian byte
slice metadata, encoding reach, and the basic mask-field distinction. Unknown
names, wrong sizes, crossing cell boundaries and out-of-range slots fail with
`ValueError`. Its register-space offsets apply to the recorded Ghidra version,
not arbitrary decoders. Scalar/pcode scratch names require separate handling.
It does not recognize opcodes, instruction bytes, broadcasts or rounding forms.
Do not interpret a successful layout check as accepting an instruction.

## Validation and assumptions

Exact commands, stdout/stderr and real exits are in `logs/`. Every compiler run
uses the wrapper read-only, `ulimit -v 2000000`, stack 65536, Dune cache disabled
and `-j1`; assumptions runs also set `PROOF_MEMORY_KB=2000000`. There was only
one compiler at a time. No shared environments or plan/status files changed.

| Log | Check | Exit |
| --- | --- | ---: |
| 04 | First build: missing fixture bool annotation, subsequently corrected | 1 |
| 05 | Seven metadata test groups, including all 96 vector view mappings | 0 |
| 06 | Exact e01 operand replay, including EVEX mask-field check | 0 |
| 07 | Dune `@e15-vector-state @smoke-x86 @smoke-ymm` | 0 |
| 08 | Rebuild final fixtures; Print Assumptions for all 15 fixture facts | 0 |
| 09 | Source admission/axiom audit of both new Rocq files | 0 |
| 10 | Equality decision procedure assumptions | 0 |
| 11 | Existing YMM lift typing assumptions | 0 |
| 12 | Clean full default Dune build (all explicitly selected modules) | 0 |
| 13 | Local primary-source version/hash/layout and runtime hash | 0 |
| 14 | Local mask-field/masking source excerpts | 0 |
| 15 | Existing scalar abs correctness/frame assumptions | 0 |
| 16 | Whole-tree source admission/axiom delta audit against pinned origin | 0 |

Reproduce metadata checks without installing anything:

```bash
/home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python -B tools/test-amd64-vector-layout.py
/home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python -B notes/e15-x86-vector-state/operand_inventory.py
```

The finite Rocq fixtures test all 32 physical widths, all eight masks, all 96
vector and 32 mask zero-upper write shapes, coexistence with the old context,
rejection of short physical writes/bad view widths/out-of-bounds reads, aliased
reads, legacy preservation, narrow zeroing, bit 511, mask bit 63, K0 versus no
writemask, a single masked byte's merge/zero alternatives, and other-slot
preservation. The synthetic ten-entry typed program also includes a 64-byte
memory load/store. Its addresses and sizes are fixtures, not binary lifts.
The single-lane mask fixture leaves other bytes unchanged intentionally; it is
not an implementation of a whole masked vector instruction.

`state_fixture_welltyped` has only the inherited assumption, verbatim:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The other fourteen fixture facts and the equality procedure print
`Closed under the global context`. The old YMM typing theorem has the same
inherited functional-extensionality assumption. This comes from the existing
typechecker theory, not a new axiom: the baseline `Picinae_statics.v`
`typctx_meet_comm` uses extensionality, and its typing soundness machinery
transitively uses the baseline update/context lemmas. No new semantic lemma kit
was added. No new admission or axiom declaration occurs in either unit source.
The existing scalar `abs_correct` also retains only inherited functional
extensionality, with its memory/callee-saved frame facts closed. All queried
Print Assumptions output is saved without editing in logs 08, 10, 11 and 15.
Build/typechecking is not a functional correctness proof or decoder proof.

## Local ancestry and handoff

Branch: `llm-proofs/e15-x86-vector-state`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-2cd37487` (delegate-prepared).
Pinned origin/merge base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Initial HEAD: reviewed e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The only imported prerequisite is exact e01
`131ad4b86cf4abcbd392048297038f3f219423bb`, joined by own merge
`1b6a4814fd989f250e771c5fa4639100b560dfe8`. All later commits are this unit's
engineering/evidence commits. See logs 01–03 and the final ancestry audit.
The first sandboxed network/local Git writes failed on access restrictions;
the read-only remote collision check, local rename and assigned local merge
then succeeded with sandbox permission. No branch collision existed. No
worktree was created and no fork history was used as a base.

No push, PR, remote comment or other remote mutation was performed. Publication
requires Charles's approval; any future PR direction is
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.

Follow-on: e17 should import this companion/metadata, translate only actual
opcode/operand forms, handle aliases, zeroing and access conditions explicitly,
and generate exact-byte, closed-CFG lifts and per-body Dune targets. e18 should
inventory additional string/mask shapes separately. General instruction
semantics/transfer lemmas belong to the separate `x-vector-instruction-lemmas`
PROOF unit under the campaign Astra-author/Sol-fixer policy. No such theorem is
implied by this state prerequisite.
