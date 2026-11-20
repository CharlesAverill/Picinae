#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
accepted=0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$accepted" HEAD
test "$(git branch --show-current)" = llm-proofs/r42-port-mask
# Every descendant of the exact accepted prerequisite must be our linear unit
# commit, with no incoming merge parent or changes outside this unit's scope.
for commit in $(git rev-list "$accepted"..HEAD); do
  test "$(git show -s --format=%P "$commit" | wc -w)" -eq 1
  git diff-tree --no-commit-id --name-only -r "$commit" | python3 -c '
import sys
paths = [x.strip() for x in sys.stdin if x.strip()]
assert all(p == "dune" or p == "Examples/FreeRTOSMask/armv6m_port_mask_proof.v" or p.startswith("notes/r42-port-mask/") for p in paths), paths
'
done
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat "$accepted"
git status --short
