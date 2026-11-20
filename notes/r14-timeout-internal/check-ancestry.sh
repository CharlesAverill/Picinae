#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=5fec2fc24d0c739bafc08add426f02a3085e15cd
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/r14-timeout-internal
git merge-base --is-ancestor "$prereq" HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat "$prereq"
git status --short
printf '\nCommits added beyond assigned prerequisite:\n'
git log --format='%H %s' "$prereq"..HEAD
printf '\nGenerated lift unchanged:\n'
git diff --exit-code "$prereq" -- Examples/FreeRTOS/vTaskInternalSetTimeOutState_armv6m.v
