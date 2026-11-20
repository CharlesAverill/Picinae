#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
e00=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
author=2d201cd4983ab0649f8d8a813158f40a7b1dbf55
head=$(git rev-parse HEAD)
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/x02-avx-nt-fix
test "$(git show -s --format=%P "$e00")" = "$base"
test "$(git show -s --format=%P "$author")" = "$e00"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
if [[ ${1:-} == --before-commit ]]; then
    test "$head" = "$author"
    test "$(git rev-list --count "$base"..HEAD)" = 2
else
    test "$(git show -s --format=%P HEAD)" = "$author"
    test "$(git rev-list --count "$base"..HEAD)" = 3
    test -z "$(git status --porcelain)"
fi
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs HEAD
git diff --stat "$author" HEAD
git status --short --branch
