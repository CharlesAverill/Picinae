#!/usr/bin/env bash
set -e
printf 'PINNED_ORIGIN='
git rev-parse origin/llm_generated_proofs
printf 'PREPARED_HEAD=71470bffba65392adf1873a3df9f0cf0ca4f1ac9\n'
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short --branch
