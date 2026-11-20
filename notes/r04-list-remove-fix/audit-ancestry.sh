#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=e74e54bdcc1b2f2cb15160c7b17417316bcac627
test "$(git branch --show-current)" = llm-proofs/r04-list-remove-fix
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$prerequisite" HEAD
diff -u notes/r04-list-remove-fix/allowed-checkpoint-commits.txt <(git rev-list "$base..$prerequisite")
for c in $(git rev-list "$prerequisite..HEAD"); do
    test "$(git show -s --format=%P "$c" | wc -w)" -eq 1
    git diff-tree --no-commit-id --name-only -r "$c" | while IFS= read -r p; do
        case "$p" in
          Examples/FreeRTOS/armv6m_uxListRemove_proof.v|notes/r04-list-remove-fix/*) ;;
          *) echo "Unexpected unit path: $p"; exit 1 ;;
        esac
    done
done
git diff --exit-code "$prerequisite" HEAD -- Picinae_armv6m.v armv6m_lifter.sh \
  Examples/FreeRTOS/uxListRemove_armv6m.v Examples/FreeRTOS/armv6m_list_model.v dune notes/r04-list-remove
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short

echo "PASS: exact checkpoint ancestry plus single-parent unit-owned commits only"
