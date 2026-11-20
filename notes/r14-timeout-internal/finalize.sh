#!/usr/bin/env bash
set -euo pipefail
test "$(git rev-parse HEAD)" = 5fec2fc24d0c739bafc08add426f02a3085e15cd
test "$(git branch --show-current)" = llm-proofs/r14-timeout-internal
git add -- dune Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.v notes/r14-timeout-internal
git diff --cached --check
git diff --cached --stat
git commit -m "Add partial timeout state proof handoff"
git rev-parse HEAD
bash notes/r14-timeout-internal/check-ancestry.sh
test -z "$(git status --porcelain)"
printf 'Final worktree status: CLEAN\n'
