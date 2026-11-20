#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=4ff26413448da4d8f064b0273ac5472cc9de7e5a
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/r03-list-insert-end
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT
{
  git rev-list "$base".."$prereq"
  for own in "$@"; do git rev-parse "$own^{commit}"; done
} | sort -u > "$expected"
git rev-list "$base"..HEAD | sort -u > "$actual"
diff -u "$expected" "$actual"
git diff --exit-code "$prereq" -- Picinae_armv6m.v lifter/armv6m.py armv6m_lifter.sh Examples/freertos/cortex-m0 'Examples/FreeRTOS/*_armv6m.v' 'Examples/FreeRTOS/*.json' Examples/FreeRTOS/armv6m_list_model.v
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat
git status --short --branch
printf 'PASS: exact allowed prerequisite plus supplied unit commits; protected artifacts unchanged\n'
