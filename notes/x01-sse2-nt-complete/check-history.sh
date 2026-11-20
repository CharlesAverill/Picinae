#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
e00=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
author=c63095989bf5d49153046d2285b3e27580346fde
checkpoint=bd8890e88451eef3ee9ce382629b8a710b95e3ed
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git show -s --format=%P "$e00")" = "$base"
test "$(git show -s --format=%P "$author")" = "$e00"
test "$(git show -s --format=%P "$checkpoint")" = "$author"
test "$(git branch --show-current)" = llm-proofs/x01-sse2-nt-complete
git merge-base --is-ancestor "$checkpoint" HEAD
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git diff --exit-code "$base" -- Examples/claude/memcpy_amd64.v
git diff --exit-code "$checkpoint" -- Examples/claude/amd64_memcpy_nt_proof.v Examples/claude/amd64_memcpy_nt_dispatch_proof.v
python3 notes/x01-sse2-nt-complete/check-declarations.py
sha256sum Examples/claude/memcpy_amd64.v notes/x01-sse2-nt-complete/original-author.v.txt
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
