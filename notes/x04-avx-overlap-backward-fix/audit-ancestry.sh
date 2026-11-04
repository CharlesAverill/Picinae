#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
e00=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
author=ac78e7a2530d77401c2fc9445c60adc48e47cb6a
checkpoint=5a6fc185901b5016d19a67c5ab9009183b756131
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
test "$(git rev-parse "$e00^@")" = "$base"
test "$(git rev-parse "$author^@")" = "$e00"
test "$(git rev-parse "$checkpoint^@")" = "$author"
git merge-base --is-ancestor "$checkpoint" HEAD
test "$(git branch --show-current)" = llm-proofs/x04-avx-overlap-backward-fix
for unit_commit in $(git rev-list "$checkpoint..HEAD"); do
  test "$(git show -s --format=%P "$unit_commit" | wc -w)" = 1
  while IFS= read -r unit_path; do
    case "$unit_path" in
      Examples/claude/amd64_memmove_avx_overlap_backward_proof.v|notes/x04-avx-overlap-backward-fix/*) ;;
      *) echo "Unexpected fix path: $unit_path"; exit 1;;
    esac
  done < <(git diff-tree --no-commit-id --name-only -r "$unit_commit")
done
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
git diff --check
git diff --exit-code "$checkpoint" -- dune notes/x04-avx-overlap-backward
echo 'PASS: exact prerequisites plus only scoped linear fix commits'
