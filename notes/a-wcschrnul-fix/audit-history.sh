#!/usr/bin/env bash
set -euo pipefail
proof_base=49956416928e5b6bb3928b54ae33e3b81091f006
proof_checkpoint=1c2abb70e24ea225674978b19053cd05b392b334
test "$(git rev-parse origin/llm_generated_proofs)" = "$proof_base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$proof_base"
test "$(git branch --show-current)" = llm-proofs/a-wcschrnul-fix
test "$(git rev-parse refs/heads/llm-proofs/a-wcschrnul)" = "$proof_checkpoint"
git merge-base --is-ancestor "$proof_checkpoint" HEAD
test "$(git rev-list --count "$proof_checkpoint"..HEAD)" -le 1
git diff --exit-code "$proof_checkpoint" -- notes/a-wcschrnul Examples/claude/lifter/scalar_ccmp dune
printf 'BRANCH='
git branch --show-current
printf 'HEAD='
git rev-parse HEAD
printf 'MERGE_BASE='
git merge-base origin/llm_generated_proofs HEAD
printf '\nCOMPLETE_ORIGIN_TO_HEAD_LOG\n'
git log --format='%H %s' origin/llm_generated_proofs..HEAD
printf '\nORIGIN_DIFF_STAT\n'
git diff --stat origin/llm_generated_proofs...HEAD
printf '\nOWN_UNIT_DIFF_STAT\n'
git diff --stat "$proof_checkpoint" HEAD
printf '\nORIGINAL_AUTHOR_BRANCH='
git rev-parse refs/heads/llm-proofs/a-wcschrnul
printf '\nSTATUS_SHORT\n'
git status --short
printf '\nDIFF_CHECK\n'
git diff --check
printf '\nPROTECTED_HASHES\n'
sha256sum notes/a-wcschrnul/initial-attempt.v.txt Examples/claude/lifter/scalar_ccmp/e30_wcschrnul_arm8.v
