# Repair setup

Unit x07-avx-rep-overlap-fix, gpt-6.1-sol, assigned xhigh/default.
Initial author gpt-6-astra. Final proof model remains unset until validation.
No delegation, installations, remote writes, or shared environment edits.

Prepared worktree /home/charles/.t3/worktrees/Picinae/t3-16637109 initially
had branch t3/avx-rep-overlap-fix, HEAD
71470bffba65392adf1873a3df9f0cf0ca4f1ac9, sole parent the pinned origin
49956416928e5b6bb3928b54ae33e3b81091f006. Initial status was clean.
The first read-only `git ls-remote --heads fork
refs/heads/llm-proofs/x07-avx-rep-overlap-fix` failed DNS (128); the
sandbox-escalated retry succeeded (0), with no output. No branch collision.
The first `git branch -m` failed because the shared Git metadata is mounted
read-only in the sandbox (128), before changing the branch. An escalated
retry renamed only the prepared branch and successfully ran
`git merge --ff-only 088a01f07128f763e9cefeb61de776795557b93e` (0).
The exact initial parent chain is recorded in 00-start.log and independently
checked by audit-ancestry.sh. The additional assigned prerequisite replaces
the common e00-only rule: e00 + accepted x03 author/fixer + x07 author
checkpoint are the complete permitted pre-unit forest.

Read plan.md (including assigned row), BUILDING.md, Examples/claude/SKILL.md,
the x07 checkpoint README/dispatch/initial-attempt/build log and the accepted
x03 source before implementation. Charles's no-admission and resource rules
supersede the skill's advice about slow proofs and increased memory caps.
Every compiler uses resource-run.py, 6000000 KiB virtual memory, stack65536,
Dune -j1, cache disabled, full vo. No compiler runs concurrently in this unit.
The gate requires write access to its own admission bookkeeping; all its
invocations are explicitly authorized sandbox escalations, without editing
the gate or its configuration.
