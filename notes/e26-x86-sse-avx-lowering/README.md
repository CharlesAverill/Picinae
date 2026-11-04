# e26: bounded AMD64 copy move/lane engineering

Completed local engineering subset; no instruction or function correctness proof.
Model/effort/tier: gpt-6.1-sol / xhigh / default, as assigned. No subdelegation.
Branch: `llm-proofs/e26-x86-sse-avx-lowering`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-473b43ee`.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No dependencies installed. Pinned e01/e02 environments and the verified Rocq
wrapper were reused read-only. Persistent mutable tool/build/project/cache state
is under `/home/charles/code/friends/.toolchains/e26-x86-sse-avx-lowering/`.
Java is bounded by `-Xmx1G`. Every Dune/Rocq/assumptions command uses
`ulimit -v 2000000; ulimit -s 65536`; Dune uses `--cache=disabled -j1`.
No cap increases, process killing, remote writes, PRs, or shared plan/status edits.

## Implementation and exact scope

`tools/ghidra-lifter/pcode2coq_x64_copy.py` subclasses the separate e25 AMD64
backend. The opt-in supervisor is `tools/ghidra-lifter/lift-x64-copy.py`.
Existing e25 source files and all e25 smoke/fixture artifacts (including receipts)
are byte-identical to checkpoint `328088263ebba11786a03448808e584231504fe1`.
The scalar profile still rejects vectors. Scalar/CET-disabled behavior is
inherited unchanged by the new copy profile; tests compare every e25 raw row.

The decoder accepts exactly the bounded 0F-map copy encodings:

| Forms | Mandatory prefix | Opcodes | Width |
| --- | --- | --- | --- |
| MOVDQU / VMOVDQU | F3 / VEX.pp=2 | 6F,7F | legacy128; VEX128/256 |
| MOVDQA / VMOVDQA | 66 / VEX.pp=1 | 6F,7F | legacy128; VEX128/256 |
| MOVUPS / VMOVUPS | none / VEX.pp=0 | 10,11 | legacy128; VEX128/256 |
| MOVAPS / VMOVAPS | none / VEX.pp=0 | 28,29 | legacy128; VEX128/256 |
| MOVNTDQ / VMOVNTDQ | 66 / VEX.pp=1 | E7, memory only | legacy128; VEX128/256 |
| VZEROUPPER | exact C5 F8 77 | 77 | low16 YMM high128 cleared |

Optional legacy REX is restricted to W=0; VEX3 is map=1,W=0, reserved
vvvv=1111. Redundant prefixes, address-size/segment/LOCK prefixes, EVEX, other
maps/opcodes, nonmemory NT forms, truncated/trailing bytes are rejected.
ModRM/SIB/displacements select actual sources, destinations and addresses;
register direction is checked for both load/store opcodes, including register
forms. Address calculation stays 64-bit and handles RIP-relative data globally.
VEX.W=1 and alternative VZEROUPPER encodings stay outside this small subset.

The entire raw-pcode DAG is checked against the independently decoded transfer:
address polynomial, memory width/read count/store count, source byte origins,
destination byte footprint and preserved bytes. It validates instruction-local
unique initialization/range overlap, all arities, memory spaces, vector base
metadata, lane extraction, and alias ordering. Legacy MOVUPS/MOVAPS lane writes
must cover all low128 bits, including self-alias cases. Unsupported/dead pcode,
mask state, GPR/flag side effects, and actual >256-bit data reads are rejected.
Raw DAGs with the same validated effects are accepted; this is an executable
symbolic gate, not a proven decision procedure or general vector translator.

Canonical cells remain `R_YMM0..R_YMM15 : 256`. Legacy128 emits a single merge
preserving bits128..255; VEX128 zeroes bits128..255; VEX256 writes all256.
Store instructions preserve source vector state. Reading the complete source in
one emitted expression avoids partial-destination alias corruption.

**Explicit ZMM projection exception:** pinned Ghidra uses 512-bit ZMM bases even
for XMM/YMM. The gate recognizes only the VEX zero-extension OUTPUT from a
validated <=256 source into its exact encoded ZMM destination; it validates the
whole zero-extension effect but emits only its low256 projection. This is not
permission to read/compute arbitrary 512-bit data. VZEROUPPER similarly checks
all96 exact constant-zero qword writes to bits128..511 of ZMM0..15, then emits
only high128 clearing in YMM0..15. Anonymous SLEIGH high qwords are allowed only
in that complete fixed zero template. Every other >256 read/write/shape and
ZMM16+, opmask or EVEX form remains rejected. e15/e17 were not imported.

The pinned VMOVNTDQ `CALLOTHER` is exactly userop303 (`vmovntdq_avx`), with one
encoded-width vector input and an instruction-local result consumed by the
validated store. Only its sequential byte value is modeled; arbitrary user-ops
are not enabled. Pinned VMOVAPS256 load pcode reads the same address twice;
that one exact duplicate-read footprint is recognized. No MMIO/concurrent
observation equivalence is asserted for this projection.

## Provenance and fixtures

Exact e01 libc: Ubuntu glibc `2.35-0ubuntu3.12`, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`.
The supervisor verifies every e01 target-manifest pin and the e02 Ghidra/JDK
archives, plus compiled x86 SLEIGH and source pins in `isa-pins.json`.
Ghidra11.4.2 raw instruction pcode only; no decompiler IR or host-libc substitute.
Global image base is 0x100000. `actual-selection.json` records ELF/global sites,
bytes, objdump spellings and exact containing copy-extent names.

`select-instructions.py` deterministically surveys all67 e01 copy extents and
selects35 instruction samples by opcode/width/direction/prefix grouping.
`actual-raw.json` preserves all35 raw decodings:31 accepted and four deliberately
rejected EVEX samples (including a <=256 YMM16 store). These isolated31-instruction
fixtures are explicitly tagged `isolated-instruction-fixtures`; there is no
fallthrough closure or whole-copy-body claim. `copy-opcodes.json` is the complete
mnemonic inventory for those copy extents, not a supported-opcode list or CFG.

`fixture/moves.S` assembles with existing GNU binutils2.42. Its pinned ELF SHA256:
`80d54e559d7069c8214eab668066f8ddc850305f96d9598817eb04f46f8db52c`.
Four selected functions (legacy21, VEX12817, VEX25615, zero2 instructions) form
one closed55-instruction synthetic union, including near RETs. Every generated
synthetic program contains that same closed union, with its own named entry.
There are51 synthetic move/zero instructions plus31 actual accepted instructions.
The raw synthetic capture also includes rejected PSHUFB and masked EVEX/ZMM
functions, excluded from generated accepted artifacts.

The assembled fixtures cover full/register self-aliases, legacy float lane
self-aliases, high registers, reverse-direction register opcodes, base/index/scale,
negative8/32-bit displacement, no-base SIB, RIP-relative load, and all move/store
families. Raw captures are made in fresh projects and verify executable hashes;
an early reused inspection project was discarded rather than accepted as evidence.
Fresh supervisor projects and nonce receipts were used for every accepted lift.

## Actual verification (exact commands and exits in logs)

All commands below run from the worktree root. `tools/record-command.sh` records
CWD, shell-escaped full command, output and real EXIT_CODE in the indicated log.

| Verification | Log under `logs/` | Actual result |
| --- | --- | --- |
| e01 deterministic sample + opcode census | selection.log | exit0 |
| Final extraction + artifact update | regenerate-pinned.log | exit0, five artifacts |
| Fresh extraction byte-for-byte replay | replay-pinned.log | exit0, .v/.json/receipts identical |
| Assembled ELF rebuild/cmp | fixture-rebuild.log | exit0 |
| Encoding/DAG/rejection/reference/receipt suite | backend-verified.log | exit0, five test groups,6560 comparisons |
| Existing e25 tests | scalar-regressions.log | exit0,12 tests |
| Existing e25 receipt tests | scalar-publication-regressions.log | exit0, one test |
| Real launcher atomic publication negatives | publication-final.log | harness exit0; four expected exit1, two expected exit2 |
| Full selected Dune project, from empty unit build directory | dune-full.log | exit0 |
| Full selected Dune project, final artifact rebuild | dune-final.log | exit0 |
| Five separate welltyped assumption queries | assumptions-verbatim.log | exit0, inherited FE only |
| Exact prerequisite + preservation audit | ancestry-precommit.log | exit0 |
| Versions | toolchain.log | Rocq9.1.1,OCaml4.14.2,Dune3.22.2 |

Finite reference comparisons use a separately parsed assembly operand description
and a byte-array oracle, evaluating emitted IL with explicit modulo64 memory
addresses. They compare every vector/GPR/flag/memory cell, including byte frame,
on80 states per instruction, with boundary and random data. These finite checks
are regression evidence, not exhaustive equivalence or an ISA correctness proof.

Actual launcher failures: supported legacy followed by PSHUFB, masked EVEX,
missing symbol, and real AVX whole-function first unsupported instruction. None
published an output directory; stage cleanup was checked. Existing output and
symlink destinations remained byte-identical. Unit tests additionally reject
partial/stale receipts, digest/profile/source mismatches, and unexpected outputs.
Earlier exploratory failure logs are retained; final passing logs above supersede
them. The full Dune build compiles the e00 selective project, not every unrelated
historical proof in Examples/claude (which includes existing admissions).

The assumptions queries report this identical inherited assumption for all five
new typing theorems (full output is saved verbatim):

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This comes through the existing Picinae static/typechecking machinery and Stdlib
functional extensionality, already present in e25 typing. No new Axiom/Parameter,
Admitted/admit or functional-correctness declaration is introduced. Typing proofs
are kernel-complete Qed. Instruction/function correctness and lifter refinement
remain separate proof units; hardware validity is not established by typing.

## Abstraction boundaries and remaining gates

* CPU feature/control state: SSE/SSE2/AVX and requisite OS vector state must be
  enabled for each encoding. The IL neither dispatches CPUID nor models XCR0,
  control-register enablement or feature exceptions.
* Memory/faults: assume canonical accessible nonfaulting full-width accesses.
  MOVDQA/MOVAPS and NT forms require their architectural alignment (16 bytes
  for128,32 for256); MOVDQU/MOVUPS permit unaligned operands but can still fault.
  These obligations are boundaries for future contracts, not runtime checks
  inserted by the lifter. The model itself uses total modulo64 byte memory.
* Sequential NT model: NT stores update the same bytes as ordinary stores here.
  Cache policy, weak ordering, fences, visibility, concurrency, interrupts,
  MMIO/volatile reads, faults/exceptions, timing and atomic publication on hardware
  are not modeled. File publication atomicity tests concern generated artifacts.
* Upper>256 state is abstracted away; no statement about preserving or zeroing
  hardware state above bit255 or interactions with future EVEX instructions.
  CET must be disabled for an ENDBR projection; shadow-stack/IBT execution is
  excluded, as in e25. Other scalar behavior is unchanged.
* No whole copy-family extraction. A real `__memmove_avx_unaligned_erms` attempt
  first rejects `JC` at global0x2a084b (scalar spelling missing from e25's gate).
  A narrow scalar alias/shift/INC/DEC/NOP/XCHG follow-on needs exact raw evidence;
  this unit deliberately does not broaden the scalar profile.
* Additional copy opcode gates from the actual census: LDDQU572; PALIGNR720
  (e34, with PSHUFB when present); REP11 and DF helpers CLD/STD (e27);
  PREFETCHNTA76/PREFETCHT0152/PREFETCHT164 and SFENCE20/LFENCE4 (e16 boundary);
  VZEROALL1; XTEST1/RTM and branch-hint/notrack/padding encodings;
  VMOVDQA6432/VMOVDQU64218 and EVEX VMOVUPS/VMOVNTDQ (e15/e17).
  Counts are disassembly mnemonic occurrences, not a closed unsupported frontier.
  Other string compare/movemask/reduction operations stay e35.
* Instruction semantic lemmas and per-function copy/return/frame specifications
  remain future proof work. There are no unresolved failures for this bounded
  engineering subset; wider forms and whole functions remain gated.

## Ancestry and publication

Pinned origin base `49956416928e5b6bb3928b54ae33e3b81091f006`;
timing reference `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` (not imported).
Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Read the shared plan and assigned e26 row before implementation. Checked a clean
prepared HEAD/base ancestry and an empty fork branch collision result, renamed
only its prepared local branch, then fast-forwarded the exact authorized
checkpoint `328088263ebba11786a03448808e584231504fe1`.
`allowed-prerequisites.txt` records the exact seven base..checkpoint commits
before edits, including only its reviewed upstream history. No other unit,
fork branch, e15 or e17 history was imported. `check-ancestry.py` checks that set,
the pinned merge-base, unit-only linear continuation and protected e25 bytes.
Before/after logs and stats accompany this note; the final SHA is in the handoff
and external unit evidence so the commit need not contain its own hash.

LOCAL ONLY. No push, PR, comments, branch deletion or remote mutation. A future
PR would require Charles's explicit approval and direction
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.
Parent alone updates shared plan/status. Suggested next engineering handoffs:
e34 copy shuffles, e27 REP/DF, e35 string vector forms; a small scalar encoding
alias audit before e06/e07 whole-body regeneration, plus explicit LDDQU coverage.
