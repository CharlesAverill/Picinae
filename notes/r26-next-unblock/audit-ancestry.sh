#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=4ff26413448da4d8f064b0273ac5472cc9de7e5a
branch=llm-proofs/r26-next-unblock
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = "$branch"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$prerequisite" HEAD
printf 'HEAD: '
git rev-parse HEAD
printf 'Merge base: '
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
for commit in $(git rev-list "$prerequisite"..HEAD); do
  test "$(git show -s --format='%P' "$commit" | wc -w)" -eq 1
  while IFS= read -r path; do
    case "$path" in
      dune|Examples/FreeRTOS/armv6m_prvResetNextTaskUnblockTime_proof.v|notes/r26-next-unblock/*) ;;
      *) printf 'UNEXPECTED path %s in %s\n' "$path" "$commit"; exit 1 ;;
    esac
  done < <(git diff-tree --no-commit-id --name-only -r "$commit")
done
git diff --exit-code "$prerequisite" -- Picinae_armv6m.v lifter/armv6m.py armv6m_lifter.sh Examples/freertos/cortex-m0 'Examples/FreeRTOS/*_armv6m.v' 'Examples/FreeRTOS/*.json' Examples/FreeRTOS/armv6m_list_model.v
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT
{ git rev-list "$base".."$prerequisite"; git rev-list "$prerequisite"..HEAD; } | sort -u > "$expected"
git rev-list "$base"..HEAD | sort -u > "$actual"
diff -u "$expected" "$actual"
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat "$prerequisite"
git status --porcelain
