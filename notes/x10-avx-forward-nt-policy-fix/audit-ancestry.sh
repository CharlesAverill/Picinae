#!/usr/bin/env bash
set -euo pipefail
test "$(git rev-parse origin/llm_generated_proofs)" = 49956416928e5b6bb3928b54ae33e3b81091f006
test "$(git merge-base origin/llm_generated_proofs HEAD)" = 49956416928e5b6bb3928b54ae33e3b81091f006
git merge-base --is-ancestor 3a3ad45b34c22a8b1e41ffd5807807c13dd3567a HEAD
git status --short --branch
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
for revision in $(git rev-list 3a3ad45b34c22a8b1e41ffd5807807c13dd3567a..HEAD); do
  git show --format='%H %P %s' --stat "$revision"
done
