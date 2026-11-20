# a-memchr-nosimd scope and initial author handoff

Author: gpt-6-astra, xhigh/default, 2026-11-03. Final proof producer is not
established by writing the sources. The final result is recorded in README.md.
No subagents, installs, remote writes, other-branch changes, or shared
campaign-file edits were performed.

Prepared worktree `/home/charles/.t3/worktrees/Picinae/t3-ba9de42a` began clean
at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`. Its parent was the pinned
origin `49956416928e5b6bb3928b54ae33e3b81091f006`. After a successful empty
`git ls-remote --heads fork refs/heads/llm-proofs/a-memchr-nosimd`, only the
prepared branch was renamed. The exact assigned prerequisite
`bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9` was fast-forwarded. The initial
sandbox blocked DNS and read-only Git metadata; authorized escalated retries
succeeded. The failure logs remain alongside the successful logs.

Seven accepted prerequisite commits, from e00 through e30, are above origin;
this is the explicit assignment's ancestry exception. The verifier checks
their exact set and constrains every later commit to this unit's files.
There is no unrelated fork, arm-validation, duneify, or fix ancestry.

## Specification

`memchr_nosimd_correct` is intended to establish `satisfies_all` for the exact
56-instruction `e30___memchr_nosimd_arm8` map. It is partial correctness, not
termination. `mc_exit` recognizes the state after RET at 0x19c894/0x19c89c.
The exit invariant requires the actual transfer to original X30, the least
matching original byte, NULL iff no match, and the frame. No result/stop-index
premise appears in the entry domain. No helper or callee contract is assumed.

Inputs are 64-bit X0=a, X1=c, X2=n. Match low8(c), preserve all memory, SP,
X19..X30, modeled R_LR, Z8..Z15, A_READ and A_WRITE. The frame for these modeled
SIMD values is stronger than their low64 ABI frame, but is not a proof of
physical vector-register refinement. No CPU feature/tunable premises or
buffer-overlap restrictions. The code model is immutable and separate from
memory. Return-address aliasing with the function map is allowed.

n=0 requires no readable envelope and allows a=0. For n>0 require a>0,
n<2^63, a+n+15<2^64, and readable bytes in
`[16*(a/16),16*((a+n+15)/16))`. The code has real widened LDPs at 0x19c7ec
and 0x19c830, and ADD X8,X7,#15. The signed CMP/MI logic requires a bounded
count; non-null makes the NULL-iff-no-hit specification meaningful in a flat
address space. All 16 pointer alignments are admitted. All prefix/suffix
padding contents are arbitrary, including matching bytes.

`mc_entry_inhabited` uses arbitrary bounded memory and a symbolic all-readable
mask. `mc_zero_entry_inhabited` covers null zero length;
`mc_all_alignments_inhabited` supplies a positive one-byte instance for every
residue 0..15, for arbitrary bounded memory and search byte. These witness
statements are not proof that program execution terminates or is fault-free.

## Proof decomposition for the fixer

1. Prove the pure `mc_detector_correct` word lemma. `(w-0x0101...) &
   ~(w|0x7f7f...)` detects zero bytes; borrows may flag later 01 bytes, so
   prove first-bit correctness rather than per-byte equivalence.
2. Relate XOR with the repeated low8 byte to byte loads, and the unaligned
   ORN/CSINV/CSEL prefix masking to `mc_scan_word` for each 8-byte half.
3. Connect the real REV and CLZ sequence to the first flagged byte. Treat
   low-word before high-word selection, and matching tail padding.
4. Establish entry, loop at 0x19c830, detector cut 0x19c840, and candidate
   cut 0x19c864. Track ZR before CCMP and X9=0 iff the block is the last.
5. Establish result at both RET sites and take the real RET step to X30.
   The post-RET trace-aware exit must be accounted for by invariant tactics.

No generated source was modified. `artifact-elf.log` verifies every encoding
against the existing pinned ELF, its SHA256, manifest hashes and map extent.
This is provenance evidence, not a semantic proof of the lifter.

The historical local tree has no `amd64_memchr*_proof.v`; read-only templates
used were `amd64_memccpy_proof.v` (mchr specification, not its contracts),
`amd64_strlen_avx2_proof.v` (first mask bit), `arm8_abs_proof.v`, and the
accepted `arm8_memcpy_small_proof.v` in another prepared worktree (witness and
frame patterns). None of those function proofs is imported as a dependency.

## Resource and validation policy

Use only the read-only shared Picinae environment through the specified
resource-run.py admission helper, cap 3000000 KiB, stack 65536 KiB, -j1,
cache disabled. The exact initial command and real exit are in
`initial-build.log`. Waiting for admission is not a compiler failure. The
initial sources are frozen verbatim as `initial-*.v.txt`, with hashes saved
before the build. No second Astra repair/build is authorized after failure.

A failed initial target must be handed to a NEW gpt-6.1-sol xhigh/default
fixer by the coordinator. Retain the statements unless genuinely wrong and
explain every statement change. Source hygiene is not an assumptions audit:
raw inline Print Assumptions output, if reached, appears in the build log.
A successful final proof must also run tools/print-assumptions.sh under the
resource gate and inspect every main theorem's transitive assumptions.
