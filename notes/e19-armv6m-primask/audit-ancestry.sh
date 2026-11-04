#!/bin/bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=95da7ab7cee78f09a528aed86c1dfaf29520a9a8
[[ $(git rev-parse origin/llm_generated_proofs) == "$base" ]]
[[ $(git merge-base origin/llm_generated_proofs HEAD) == "$base" ]]
git merge-base --is-ancestor "$prereq" HEAD
[[ $(git branch --show-current) == llm-proofs/e19-armv6m-primask ]]
# Any commits after the reviewed prerequisite must be the supplied own SHAs.
actual=$(git rev-list "$prereq"..HEAD | sort)
expected=$(for own in "$@"; do git rev-parse "$own"; done | sort)
[[ "$actual" == "$expected" ]]
git merge-base origin/llm_generated_proofs HEAD
git log --oneline origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
printf '\nUnit worktree diff since reviewed checkpoint (includes uncommitted tracked edits):\n'
git diff --stat "$prereq"
printf '\nPASS: exact allowed prerequisites plus supplied own commits only\n'
