#!/usr/bin/env bash
# Read-only final ancestry/status audit. Run after the local handoff commit.
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git rev-parse "$prereq^")" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
test "$(git branch --show-current)" = llm-proofs/x03-avx-overlap-forward
git merge-base --is-ancestor "$prereq" HEAD
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --exit-code "$base" -- Examples/claude/memmove_avx_amd64.v
git status --short
test -z "$(git status --porcelain)"
