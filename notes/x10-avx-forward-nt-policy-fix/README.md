# x10 AVX forward NT-policy repair

Status: PARTIAL / WIP; stopped on Charles's explicit wrap-up order.
No full x10 target or transitive assumptions audit succeeded. Initial author: OpenAI gpt-6-astra, xhigh/default.
Repair author: OpenAI gpt-6.1-sol, xhigh/default. Final proof producer pending.

Assigned local branch: llm-proofs/x10-avx-forward-nt-policy-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-5fe56d14.

Prepared HEAD was e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9,
with sole parent pinned origin 49956416928e5b6bb3928b54ae33e3b81091f006.
Initial status was clean before evidence creation. The read-only remote
collision check succeeded with no result before renaming. Sandbox DNS and
Git-metadata writes initially failed; authorized retries succeeded. Imported
only the assigned exact source checkpoint
3a3ad45b34c22a8b1e41ffd5807807c13dd3567a via fast-forward. Its complete
ancestor set above origin is the allowed prerequisite history; no additional
branch or remote was changed.

All compiler/query commands run through the shared resource-run.py gate with
unit x10-avx-forward-nt-policy-fix and memory 4000000 KiB. The gate enforces
the same hard virtual-memory cap and stack 65536 KiB; Dune uses -j1,
--cache=disabled and mode vo. No installation or shared environment change.
No subagents, publication, remote writes, or other-unit process changes.

The exact original source is retained under
notes/x10-avx-forward-nt-policy/initial-attempt.v.txt, together with unchanged
Astra diagnostics and handoff evidence. audit-preservation.py compares every
original theorem statement and definition verbatim, and verifies the original
map and both x03/x02 prerequisite proof forests are byte-identical to the
checkpoint. No Dune changes are necessary: the checkpoint already lists the
exact target and prerequisite modules explicitly.

Repairs so far: restore archived proof bodies and replace ofnt_negative_gap's
failed rewrite by explicit unsigned bounds. For d<s<2^64, 0<s-d<2^64 and
(d-s) mod 2^64 = 2^64-(s-d); a second modular negation is exactly s-d.
No theorem statement or definition is changed.

The intended unchanged domain is 256<n<2^63, d<s<d+n, s+n<=2^64,
n<=the original-memory quadword at 0x31a3f8, and original-memory quadword at
0x3215a8<n. No additional gap, threshold, separation, CPU or result premise.
The original-memory byte-copy/frame result and RAX=d/RSP=rsp hold at the cut
before RET 493; RBX/RBP/R12-R15 are preserved. This is sequential lifted-IL
partial correctness, with inherited unvalidated lifting provenance, no
termination or executed-RET claim. Starting REP-selected inputs remain x07.
The actual NT-policy branch 331 reaches 813, negates d-s to s-d and falls
back at 819 to 363 for every genuine forward overlap; no nonoverlap NT
functional theorem is applied to these overlapping inputs.

Evidence files record exact commands, stdout/stderr and actual exit codes.
Fresh assumptions output is required before a completion claim. The baseline
inherited FunctionalExtensionality.functional_extensionality_dep is expected
but must be confirmed transitively; imported admissions disqualify completion.


## Ordered wrap-up

Charles ordered immediate stop, no new work/retries. Only this unit's compiler
process tree was terminated. The shared gate released its lease with exit=-15
(wrapper exit 143). No memory-cap failure was reported. The log reached x03
prerequisite output; no completed x10 .vo or fresh assumptions query exists.
The proposed explicit-bounds repair and restored original bodies are preserved
in stopped-repair.v.txt, with all original statements/definitions unchanged.
All unvalidated bodies from ofnt_negative_gap onward are Abort in the active
proof source, preserving the original four prefix Qeds. No new admissions,
axioms or parameters. No new x10 theorem is claimed proved. Next: restore the
archived repair, run the gated full target, repair actual diagnostics, then
run the saved assumptions and preservation/source audits. No publication.
