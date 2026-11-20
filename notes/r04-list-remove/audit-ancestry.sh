#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=4ff26413448da4d8f064b0273ac5472cc9de7e5a
test "$(git branch --show-current)" = llm-proofs/r04-list-remove
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$prerequisite" HEAD
diff -u notes/r04-list-remove/allowed-prerequisites.txt <(git rev-list "$base..$prerequisite")
for c in $(git rev-list "$prerequisite..HEAD"); do
    test "$(git show -s --format=%P "$c" | wc -w)" -eq 1
    git diff-tree --no-commit-id --name-only -r "$c" | while IFS= read -r p; do
        case "$p" in
          dune|Examples/FreeRTOS/armv6m_uxListRemove_proof.v|notes/r04-list-remove/*) ;;
          *) echo "Unexpected unit path: $p"; exit 1 ;;
        esac
    done
done
git diff --exit-code "$prerequisite" HEAD -- Picinae_armv6m.v armv6m_lifter.sh \
  Examples/FreeRTOS/uxListRemove_armv6m.v Examples/FreeRTOS/armv6m_list_model.v
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
