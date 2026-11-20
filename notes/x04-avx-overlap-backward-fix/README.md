# x04 AVX backward overlap repair

State: **DONE for the retained sequential IL partial-correctness scope**.
All 23 original results are Qed, all 11 definitions are retained, and there
are no admissions or new axioms/parameters. The first successful target is
in `10-build.log`; final-source rebuild and assumptions certification are
in `13-final-build.log` and `14-assumptions.log` (all exit 0).
No remaining proof gaps exist within these statements; the execution and
provenance limits below remain explicit.
Original author: OpenAI gpt-6-astra, xhigh/priority. Final proof producer:
OpenAI gpt-6.1-sol, xhigh/priority. Work done without subagents.

Branch: `llm-proofs/x04-avx-overlap-backward-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-4b9b461e`.
All work is local: no push, PR, remote comments, or other remote writes.
No installation, shared toolchain mutation, or campaign file edits.

## Contract and limits

`memmove_avx_correct_overlap_backward` proves `satisfies_all` on the unchanged
`memmove_avx_amd64` map from entry 0 to the invariant at RET 623, under exactly
`bw_domain d s n`: n>256, s<d<s+n, 128<=d, d+n<=2^64, s+n<=2^64,
plus the stated typed-entry/register/memory/trace-start hypotheses. The
postcondition gives RAX=d, unchanged RSP, destination bytes equal to ORIGINAL
source bytes, and all bytes outside destination unchanged. There is no NOV,
DF, CPU-policy, threshold, minimum-gap, or arbitrary size-cutoff premise.
The absolute 128<=d protects the real cursor subtraction; it is not a
minimum overlap distance. `bw_domain_all_gaps`, `bw_gap_examples`, and the
typed witness cover every genuine gap at n=257, including 1,31,32,127, and
the general arithmetic domain admits every 0<gap<n subject to nonwrap.

`memmove_avx_correct_self_alias` proves the actual d=s,n>256 early-return
path to RET 493, with whole memory, RSP, and return value preserved as
specified. Its domain has no additional nonwrap or lower-address premise.
`memmove_avx_overlap_backward_at_ret` and `memmove_avx_self_alias_at_ret`
extract these results for actual `exec_prog` traces ending at those RETs,
with the explicit `unterminated` hypotheses.

Both dispatches 309 and 704 compare d-s with n and branch to 496 before
NT/REP policy. Thus an arbitrary initial REP threshold is permitted. The
nonzero gap takes the backward loop; zero takes VZEROUPPER and RET 493.
No NONOVERLAP loop, REP, NT, or assumed callee contract is imported.

`bw_suffix_unread` and `bw_loop_unread` derive the original unread-source
prefix from the copied suffix/frame. `bw_store4` proves four stores whose
four loads all precede any store. The loop invariant preserves saved original
head vectors YMM0/5/6/7 and original last vector YMM8 for the final stores.
`memmove_avx_overlap_backward_preserves_callee_saved` is a real
`forall_endstates` frame for RBX,RBP,R12-R15. Separate welltyped and
no-write-code facts are also checked.

The typed zero-permission entry witness establishes satisfiability of the
register/arithmetic domain, and `bw_initial_memory_satisfiable` establishes
the empty copied set and original unread prefix. The witness has
A_READ=A_WRITE=0: it does NOT establish an accessible execution or termination.
No new callee or execution contract requires a separate assumed witness.

All results are sequential IL partial correctness. Neither termination,
execution of RET/caller continuation, physical mapped memory, CPU feature
availability, fault/timing/cache/concurrency behavior, nor binary/lifter
soundness is established. Binary provenance is inherited, not independently
validated: Ubuntu glibc 2.35-0ubuntu3.12, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
`__memmove_avx_unaligned_erms`, Ghidra 0x2a0840/imagebase 0x100000.

## Repair and validation

Every original definition/predicate and all 23 theorem statements are
retained exactly apart from whitespace/comments. The declaration checker
compares entire statements AND definition bodies against the archived initial
attempt, rather than only comparing declaration names. No false statement
needed correction, and no supporting theorem was added.

The archived scripts were restored. Repairs were limited to:

- proving the concrete gap examples by unfolding `bw_domain` and `lia`;
- passing PRE explicitly to the dispatch tactic (the original free PRE was
  not in scope while defining the tactic);
- separating 0<d-s<n into individual facts, which the arithmetic pruning
  tactic retains when refuting the impossible dispatch branch;
- making the gap rewrite optional because self-alias simplifies it already.

Original evidence in `notes/x04-avx-overlap-backward/` is preserved unchanged.
Logs 04,06,07,08,09 retain every failed iteration and exact diagnostic/exit
status. Log 10 is the first successful full `.vo` build, not a `.vos` check.
The final-source build uses the same explicit target and shared read-only
`picinae-env`, `ulimit -v 6000000`, `ulimit -s 65536`, `--cache=disabled -j1`.
The assumptions helper is likewise capped by PROOF_MEMORY_KB=6000000 and
PROOF_STACK_KB=65536; proof compilers run sequentially. The inherited Dune
module selection is unchanged and contains only this target plus its needed
shared dependencies, without globs.

Source audit 11 reports no current or new admission/axiom/parameter tokens
in the target. Protected-source audit 12 confirms the generated lift, core
and shared proof sources are unchanged from the pinned origin base.

## Ancestry

Prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is origin base `49956416928e5b6bb3928b54ae33e3b81091f006`.
Initial status was clean before creating the unit evidence directory; the
recorded before-status contains only that directory. The required read-only
fork collision check succeeded, exit 0 with no result (log 01), after a first
sandbox DNS failure in the tool transcript. Only the prepared branch
`t3/avx-overlap-backward-fix` was renamed (log 02). Log 03 fast-forwards to
the exact authorized checkpoint `5a6fc185901b5016d19a67c5ab9009183b756131`.
Its only additional ancestor is author commit
`ac78e7a2530d77401c2fc9445c60adc48e47cb6a`. No fork history, other active
unit, or unrelated branch was imported or changed. Final ancestry, diff,
and clean status are recorded separately.

## Transitive assumptions certificate

All 23 original results were passed to `tools/print-assumptions.sh`, which
rebuilt the final whitespace-cleaned source as a full `.vo` before compiling
the queries. `14-assumptions.log` preserves the raw stdout/stderr and true
exit 0. `21-assumptions-review.log` checks every certificate: 18 are closed
under the global context, five have only inherited functional extensionality.
Those five are the welltyped theorem, both main correctness theorems, and
both RET corollaries. Every witness, unread-source/memory helper and callee
frame theorem is closed. There is no imported admitted proof.

Verbatim assumptions block for each main theorem and RET corollary:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the existing Stdlib assumption documented in e00's
`notes/e00-build/logs/15-extensionality-provenance.log`, imported through
Picinae's baseline theory/simplifier. It is not a new unit axiom.
The full-tree source audit (16) passes with NEW totals {}; inherited
admissions elsewhere are not selected or imported by these proofs. The
final scoped audit (23) has BASELINE/CURRENT/NEW totals all {}.

Log 17 intentionally preserves a failed precommit whitespace check: two
trailing spaces inherited from the original scripts. They were removed,
and logs 18/22/23 verify the final diff/declarations/source. The final
assumptions helper rebuilt after that whitespace-only change.

Successful commands (through the shared read-only environment wrapper):

```bash
ulimit -v 6000000
ulimit -s 65536
dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_overlap_backward_proof.vo
```

The full 23-name assumptions command is recorded exactly in log 14, with
`PROOF_MEMORY_KB=6000000 PROOF_STACK_KB=65536`.
