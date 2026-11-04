# x04 AVX backward overlap — PARTIAL

Author: OpenAI gpt-6-astra, xhigh/priority. Final proof model: none (PARTIAL).
Branch: `llm-proofs/x04-avx-overlap-backward`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-53ef439b`.

## Provenance and ancestry

Initial HEAD was exactly `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole
parent and merge base against origin/llm_generated_proofs were
`49956416928e5b6bb3928b54ae33e3b81091f006`. Initial `git status --short` was empty
before creating this evidence directory. The recorded before-status contains
only that newly created directory. No merge/import was necessary.

The first `git ls-remote --heads fork refs/heads/llm-proofs/x04-avx-overlap-backward`
returned exit 0 and empty output in the tool transcript. A subsequent attempt
through record-command failed with DNS resolution error (exit 128), retained
verbatim in 01-branch-name-check.log. Only the new prepared local branch
`t3/x04-avx-overlap-backward` was renamed. The initial sandbox rename failed
because Git metadata was read-only; the authorized escalated rename succeeded
(exit 0 in 02-branch-rename.log). No other branch was changed. No remote writes.

Lift: unchanged `Examples/claude/memmove_avx_amd64.v`, inherited Ubuntu amd64
glibc 2.35-0ubuntu3.12, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`, symbol
`__memmove_avx_unaligned_erms`, Ghidra 0x2a0840/imagebase 0x100000, normalized
entry 0. This unit does not independently establish binary/lifter soundness.

## Contracts and dispatch inspection

`memmove_avx_correct_overlap_backward` is an entry-to-RET 623 partial-correctness
statement over the actual unchanged IL, with `bw_domain` requiring n>256,
s<d<s+n, 128<=d, d+n<=2^64 and s+n<=2^64. The source bound follows from the
other bounds but remains explicit. Output is RAX=d, RSP unchanged, every
original source byte copied, and every byte outside destination unchanged.
`memmove_avx_overlap_backward_at_ret` extracts the RET postcondition.

`memmove_avx_correct_self_alias` specifies the actual early-return path to
RET 493, for d=s and n>256, with whole memory unchanged. Its separate invariant
marks the first head-save instruction 501 unreachable. It does not merely
assert the mathematical identity copied m m. `memmove_avx_self_alias_at_ret`
extracts the corresponding RET postcondition.

The separate no-write-code, welltyped and real callee-saved frame declarations
reuse the baseline small proof's established generic facts. The frame is
RBX,RBP,R12,R13,R14,R15 under forall_endstates. RSP is unchanged at the RET
instruction; executing RET and returning to a caller are NOT claimed.

Dispatch at 309 computes d-s, compares it with n, and branches at 318 to 496
before NT policy. Dispatch at 704 (sizes above the threshold at 0x31a3f8)
performs the same comparison and branches at 713 to 496 before REP policy.
At 496 the zero difference takes JZ 499 to VZEROUPPER 490 / RET 493.
Nonzero difference loads saved head/tail values, computes the aligned cursor
floor32(d+n-129), and enters the backward loop at 544. There is no threshold,
CPU-policy, DF, NOV, minimum-gap, or arbitrary size-cutoff premise.
ISA availability, faults, concurrency, cache, and timing are outside the IL
model. No claim of termination or hardware/binary correctness is made.

The absolute destination bound 128<=d is retained because the loop subtracts
128 from its absolute cursor before the unsigned comparison at 590. It is not
a minimum source-destination gap. The proposed witnesses include every gap
1..256 at n=257, with concrete 1,31,32,127 cases, plus a general all-gaps domain
lemma with the natural address bound. The typed witness has source 4096,
destination 4096+gap, length 257, stack pointer 8192, and zero original memory.

The proposed suffix memory invariant records offsets
[c-d+128,c0-d+128) already copied and unchanged memory elsewhere.
`bw_suffix_unread` derives preservation of source[0,k) when all written
destination offsets are >=k and s<=d. `bw_store4` uses that fact for four
loads taken before any stores. `bw_loop_unread` exposes the unread-source
property of the actual loop invariant. YMM0/5/6/7 preserve original head
loads and YMM8 preserves the original final 32 bytes. No global source
preservation is asserted after overlapping writes. No callee/loop contract
is assumed; no NONOVERLAP loop, REP or NT theorem is imported.

## Validation policy

`initial-attempt.v.txt` is the exact source submitted to the only initial
full-target build. The root Dune module list adds only the target and its
four missing dependencies: memcpy_sets, memcpy_lemmas, memmove_avx lift,
and the baseline small AVX proof. There are no globs and no imported unit
history. The existing read-only environment wrapper is used, with
`ulimit -v 6000000`, `ulimit -s 65536`, `--cache=disabled -j1`, and full `.vo`.
No installation or shared environment modification occurred.

All logs use tools/record-command.sh. The initial scoped and full source
audits pass with NEW totals {}. Baseline admissions elsewhere in the repo
remain inventoried, not selected or used. Source scanning is not a transitive
assumptions certificate. The selected source dependency review is in log 07.
Inherited Stdlib FunctionalExtensionality.functional_extensionality_dep is
known from e00; acceptance still requires raw Print Assumptions for this unit.

## Initial-build failure and mandatory handoff

State: **PARTIAL**, not done. The only full target command (log 05) exited 1.
The baseline dependency `amd64_memmove_avx_proof.vo` completed successfully,
then the new target failed at original source line 92, characters 33-44:

```
Error: Cannot find a relation to rewrite.
```

This is the `vm_compute; repeat split; reflexivity` attempt for
`bw_gap_examples`. This diagnostic was NOT repaired. No second Astra build,
interactive proof session, or repair cycle was run. No memory cap increase
was requested or applied.

The compiler passed the Qed boundaries of `bw_suffix_unread` and
`bw_domain_all_gaps` before this error. Their original proof bodies are
retained. This does not constitute a successful full target or assumptions
certificate. All subsequent unchecked lemma/theorem/corollary proof bodies
were replaced by Abort, with EXACT statements retained. The entire original
attempt is preserved in `initial-attempt.v.txt`. The sanitized handoff source
has not been rebuilt. No newly exported main theorem exists.

No successful target command for this unit exists. `tools/print-assumptions.sh`
was not invoked: it rebuilds the target, and after this failure the explicit
one-build policy requires immediate handoff. Consequently there is no raw
unit assumptions output, no certified transitive assumption closure, and no
claim that inherited functional extensionality is the only assumption of
these proposed main proofs. e00 documents inherited
`FunctionalExtensionality.functional_extensionality_dep`; the new Sol fixer
must run and inspect the required per-theorem/helper/frame/witness queries.

Coordinator action: launch a NEW gpt-6.1-sol xhigh/priority fixer, retaining
the statements unless genuinely wrong and explaining every change. Restore
initial bodies from the preserved attempt as needed. The main backward
entry/dispatch/loop/final-store proof, self-alias early exit, typed witnesses,
RET corollaries, and assumption audits all remain unverified. This unit has
no complete entry-to-RET proof. It does not inherit any accepted NT unit.
