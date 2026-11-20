#!/usr/bin/env bash
# Read-only local audit. Argument(s) must be this unit's own implementation commits.
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/e05-freertos-lifts
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT
{
    # Reviewed e00, e03 original + prerequisite integration + validation, e04.
    git rev-list "$base"..5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b
    printf '%s\n' abe7eda601a63d47eb70e765f4ae2c4ca235cca4
    # Own clearly named e05 prerequisite integration commit.
    printf '%s\n' 8c01958e73ec7fe959c60b29444505afbb599d13
    for own in "$@"; do git rev-parse "$own^{commit}"; done
} | sort -u > "$expected"
git rev-list "$base"..HEAD | sort -u > "$actual"
diff -u "$expected" "$actual"
git diff --exit-code 5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b -- Picinae_armv6m.v lifter/armv6m.py armv6m_lifter.sh
git diff --exit-code abe7eda601a63d47eb70e765f4ae2c4ca235cca4 -- Examples/freertos/cortex-m0 ':!Examples/freertos/cortex-m0/extract.py'
git merge-base origin/llm_generated_proofs HEAD
git log --oneline origin/llm_generated_proofs..HEAD
git log --format='%H %P %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat
git status --short --branch
printf 'PASS: exact assigned ancestry; e03 ISA/frontend and e04 fixture unchanged\n'
