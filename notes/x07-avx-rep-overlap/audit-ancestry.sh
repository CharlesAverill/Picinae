#!/usr/bin/env bash
set -eu
base=49956416928e5b6bb3928b54ae33e3b81091f006
checkpoint=14ea393f2227bc8bde692b1e70badc61dce80304
branch=$(git branch --show-current)
test "$branch" = llm-proofs/x07-avx-rep-overlap
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$checkpoint" HEAD
git branch --show-current
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %P %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat
git status --short
git diff --exit-code "$base" -- Examples/claude/memmove_avx_amd64.v
