# a-memcpy-large

**PARTIAL / UNVALIDATED WIP — Charles ordered immediate wrap-up.**
The resource gate never admitted the queued first build. It was stopped on
Charles's instruction before any compiler started. Zero current-unit theorems
are certified; the source is an untested initial attempt, not a checked proof.
No compiler failure or memory-cap failure was observed. No assumptions query
was run. All execution obligations remain open. No new admissions or axioms
were introduced. The archived attempt and current source are unchanged.
Next step: coordinator-controlled initial full build through the resource gate;
if it fails, hand off the preserved statements to the mandated Sol fixer.

Initial author: OpenAI gpt-6-astra, xhigh/default, 2026-11-03.
Final proof producer: not established. Local only; no publication.
Branch: `llm-proofs/a-memcpy-large`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-9fd9a36c`.

## Scope and statements

The proposed `memcpy_large_correct` starts at actual public entry `0x19ab40`
and follows the unchanged generated e08 scalar map through the alignment head,
64-byte loop and tail to the RET cut at `0x19acc8`. It states `satisfies_all`;
it does not execute RET or prove termination. The direct reached-exit statement
is `memcpy_large_returns_original_bytes`; the projected ABI frame is
`memcpy_large_preserves_callee_saved`.

The initial typed store has memory m, X0=d, X1=s and X2=n. The domain is exactly
n>128, d+n<=2^64, s+n<=2^64, modular nonoverlap, readable source bytes and
writable destination bytes. No extra pointer lower bound, strict endpoint,
n<2^63, CPU-feature or tunable premise is imposed. Size <=2^63 is derived from
NOV and nonwrapping. The postcondition requires ORIGINAL source bytes in every
destination byte, all outside bytes unchanged, X0=d and preservation of SP,
X19..X30, the separate modeled R_LR, and entire Z8..Z15 values.

The provenance is inherited: Ubuntu ARM64 glibc 2.35-0ubuntu3.15 libc,
SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06;
Ghidra 11.4.2 explicit strict scalar e08 replacement; model addresses are ELF
addresses +0x100000. No lifter/hardware/binary refinement is established here.
The common helpers, small proof, generated program and maps remain unchanged.
No medium or final-composition work is included.

`initial-arm8_memcpy_large_proof.v.txt` preserves the exact initial source,
including every statement, definition, tactic and attempted proof. The only
build attempt is recorded verbatim in `first-build.log`. Its command enters the
shared resource gate with 4000000 KiB memory, 65536 KiB stack, one compiler and
Dune cache disabled. No dependencies were installed or shared envs changed.

## Invariant design

At loop/tail, q is the positive offset of the first buffered qword. X6..X13
contain the eight ORIGINAL memory loads at s+q+8j, j=0..7. The memory fact is
`cpy m M d s (fun i => i<16 \/ i<q)`. X3 is `(d+q)-16` modulo 2^64,
X1 is s+q+48 modulo 2^64, X4/X5 are the modular source/destination ends.
At head, q=16-(d mod 16). Its source cursor s-(d mod 16) may underflow.

Loop requires q+128<n and X2=n-(q+128). Each iteration stores [q,q+64),
loads the next block and advances q by 64. Tail requires q+64<=n<=q+128.
It stores the pending block and [n-64,n); these intervals and the written
prefix cover [0,n). `cpy_load` is the intended justification of all loads
performed after stores. Nonoverlap keeps original source bytes available.
The post-state assertions are not execution premises.

The generic entry witness has arbitrary typed memory and fully permitted
memory. Concrete witness statements cover (d,s,n)=(4095,0,129) and
(0,2^64-129,129), respectively alignment-source underflow and modular end 0.
`check-offset-model.py` additionally checked 63520 count/residue cases,
including n=2^63. That finite arithmetic check is NOT an IL/proof certificate.

## History and evidence

Prepared HEAD was e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9, with sole parent
49956416928e5b6bb3928b54ae33e3b81091f006. Initial tool output showed clean status;
`ancestry-before.log` was made after creating this unit's notes directory, so
it honestly shows that directory as untracked. The first sandboxed remote
query could not resolve github.com; the escalated read-only query succeeded
with no result before rename. `collision-check.log` records a repeated empty
successful query. The first sandboxed ff-only import could not create
ORIG_HEAD.lock; the escalated import succeeded without changing the planned
history. Only the prepared branch was renamed.

The exact assigned prerequisite is 1eb19d19c77636496bb24c6c9c53c029ac76935b.
Its seven commits above origin are e00 plus 081d0233,052521a7,378fe1b5,
9ae8e680,473a40d2,1eb19d19. `audit-ancestry.py` verifies the exact ancestor
set, pinned origin, merge base and new commit/file scope. Raw import, branch,
source and protected-input audits accompany this document.

Inherited dependency assumptions must be disclosed: baseline and accepted
prerequisite evidence document FunctionalExtensionality.functional_extensionality_dep.
No imported admitted proof is acceptable. Raw output from this attempt is the
only current-unit assumptions evidence until a successful full build and
`tools/print-assumptions.sh` run are available.
