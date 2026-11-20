#!/bin/bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6
[[ $(git rev-parse origin/llm_generated_proofs) == "$base" ]]
[[ $(git merge-base origin/llm_generated_proofs HEAD) == "$base" ]]
git merge-base --is-ancestor "$prereq" HEAD
[[ $(git branch --show-current) == llm-proofs/e20-armv6m-critical ]]
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
