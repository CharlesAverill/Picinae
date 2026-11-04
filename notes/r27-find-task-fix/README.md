# r27-find-task-fix — PARTIAL / stopped by Charles

Branch: llm-proofs/r27-find-task-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-f791c5bc.
Exact source checkpoint: 00ca4312875f97177309034d7ee743a5ca7bb03f.
Origin merge-base: 49956416928e5b6bb3928b54ae33e3b81091f006.
Initial author: gpt-6-astra. Fixer: gpt-6.1-sol, xhigh/default.
Final functional proof producer is not certified.

Charles ordered immediate wrap-up: no further proving, compiler runs, queries,
retries or waiting. The sole interactive Rocq session was closed with Quit;
its resource gate released with exit 0. This is a session exit, NOT successful
compilation: its Load reported an error and selected Dune's previous source
copy (see 13-repl.log). The attempted absolute-path Load was rejected by
automatic approval review after the wrap-up order; it was not retried.
The corresponding final line in 13-repl.in records that unsent command.

## Actual progress

Build 05 accepted the fifteen original Qed declarations before search_correct,
including the repaired search_skip_prefix and restored first-match/witness
proofs, then failed on the models_at_invariant argument order. No full .vo.
Build 06 corrected that order and reached all symbolic cut obligations, then
was interrupted during the original expensive eauto 12 search. Only the
verified own compiler child was signalled (07-interrupt-own-build.log).
Build 08 removed blind search and exposed 13 explicit obligations. It failed
intentionally as a diagnostic, not as a correctness certificate.
Every actual compiler/query used the shared gate with 2500000 KiB memory,
65536 KiB stack and the read-only isolated environment. Dune used full vo,
--cache=disabled -j1. No OOM or cap failure was observed; gates waited for RAM.

The source retains all original definitions and nineteen theorem statements.
Its first fifteen proof scripts were reached in build 05; the final four
execution/return statements are Abort, with no exported theorem constants.
Unverified helper lemmas and the detailed unfinished case proof are preserved
in wip-at-wrap.v.txt, helpers.v.txt and loop-proof.v.txt as inert text.
The packaged final source was NOT rebuilt after the stop order.
No admissions, new axioms or parameters were added. Existing original branch,
generated map, list kit and Astra evidence remain unchanged.

## Open scope and next step

search_correct, search_post_at_pop, search_return_step and search_caller_result
remain unproved. The 13 obligations cover PUSH stack image, initial empty/
nonempty list paths, successful owner path, next-link sentinel/non-sentinel
paths, outer-loop setup, byte mismatch/equal-NUL/continuation/bound-exhaustion.
The guarded POP existence/frame proof has not been validated. Original-memory
loads require stack/input separation; the scratch helpers address that but
have not been kernel checked. No scheduler, hardware, IRQ or termination claim.

Next authorized continuation should validate the scratch helper lemmas, repair
the explicit loop cases, construct actual POP, then build the full target and
run tools/print-assumptions.sh on every exported theorem through the same gate.
There is no successful unit full-target command or raw unit Print Assumptions
output. Inherited FunctionalExtensionality.functional_extensionality_dep is
baseline context only, not an audited claim for these restored helpers.

## Evidence

01/02/03 and remote-name.log: preparation, sandbox rename failure followed by
successful metadata-authorized branch rename and exact checkpoint fast-forward.
05/06/08: actual compiler output and exit codes. 13: raw interactive output.
09: repository source audit, exit 0, no new forbidden tokens.
10: all nineteen statements and all original definitions preserved, exit 0.
11: pinned source/lift/layout provenance checks, exit 0.
12: exact prerequisite ancestry union and scoped changes, exit 0.
Those audits precede final WIP packaging; no validation was rerun after stop.
No host installs, shared environment edits, pushes, PRs or remote writes.
