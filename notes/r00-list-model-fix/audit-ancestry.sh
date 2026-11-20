#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=95da7ab7cee78f09a528aed86c1dfaf29520a9a8
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/r00-list-model-fix
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT
{
  printf '%s\n' \
    71470bffba65392adf1873a3df9f0cf0ca4f1ac9 \
    59f696d32a5623cdfbceb9a1e0f91e2cc7c054c1 \
    dac36c0a03088a90bb6e6385f82cb355d27cc204 \
    5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b \
    abe7eda601a63d47eb70e765f4ae2c4ca235cca4 \
    8c01958e73ec7fe959c60b29444505afbb599d13 \
    075f59aca328e60e6376e2af01fa49925ab10e9d \
    95da7ab7cee78f09a528aed86c1dfaf29520a9a8 \
    7de9edcc1e5094133d66bbeae129ef48078b9265
  for own in "$@"; do git rev-parse "$own^{commit}"; done
} | sort -u > "$expected"
git rev-list "$base"..HEAD | sort -u > "$actual"
diff -u "$expected" "$actual"
git diff --exit-code "$prereq" -- Picinae_armv6m.v lifter/armv6m.py armv6m_lifter.sh Examples/freertos/cortex-m0 'Examples/FreeRTOS/*_armv6m.v' 'Examples/FreeRTOS/*.json'
git diff --exit-code 7de9edcc1e5094133d66bbeae129ef48078b9265 -- notes/r00-list-model dune
while IFS= read -r path; do
  case "$path" in
    Examples/FreeRTOS/armv6m_list_model.v|notes/r00-list-model-fix/*) ;;
    *) printf 'Unexpected fixer change: %s\n' "$path" >&2; exit 1 ;;
  esac
done < <(git diff --name-only 7de9edcc1e5094133d66bbeae129ef48078b9265 --)
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat
git status --short --branch
printf 'PASS: exact accepted prerequisite and supplied own commit set; protected artifacts unchanged\n'
