#!/usr/bin/env bash
set -e
printf 'HEAD='
git rev-parse HEAD
printf 'BRANCH='
git branch --show-current
printf 'ORIGIN='
git rev-parse origin/llm_generated_proofs
printf 'AUTHOR_BRANCH='
git rev-parse llm-proofs/a-ffsl
printf 'MERGE_BASE='
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short --branch
