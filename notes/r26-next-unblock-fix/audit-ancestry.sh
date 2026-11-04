#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
checkpoint=9cdc8b9ede899efa594dc84a55f33e85616c9091
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/r26-next-unblock-fix
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$checkpoint" HEAD
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
for commit in $(git rev-list "$checkpoint"..HEAD); do
  test "$(git show -s --format='%P' "$commit" | wc -w)" -eq 1
  while IFS= read -r path; do
    case "$path" in
      Examples/FreeRTOS/armv6m_prvResetNextTaskUnblockTime_proof.v|notes/r26-next-unblock-fix/*) ;;
      *) printf 'UNEXPECTED path %s in %s\n' "$path" "$commit"; exit 1 ;;
    esac
  done < <(git diff-tree --no-commit-id --name-only -r "$commit")
done
git diff --exit-code "$checkpoint" -- dune Picinae_armv6m.v lifter/armv6m.py armv6m_lifter.sh Examples/freertos/cortex-m0 'Examples/FreeRTOS/*_armv6m.v' 'Examples/FreeRTOS/*.json' Examples/FreeRTOS/armv6m_list_model.v notes/r26-next-unblock
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat "$checkpoint"
git status --porcelain
