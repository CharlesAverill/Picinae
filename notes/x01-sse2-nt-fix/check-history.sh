#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
author=c63095989bf5d49153046d2285b3e27580346fde
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git rev-parse "$prerequisite^")" = "$base"
test "$(git rev-parse "$author^")" = "$prerequisite"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$author" HEAD
test "$(git branch --show-current)" = llm-proofs/x01-sse2-nt-fix
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --exit-code "$prerequisite" -- Examples/claude/memcpy_amd64.v
printf '\nGenerated lift baseline/current hashes:\n'
git show "$prerequisite:Examples/claude/memcpy_amd64.v" | sha256sum
sha256sum Examples/claude/memcpy_amd64.v
printf '\nWorking status:\n'
git status --short
