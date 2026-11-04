#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e26-x86-sse-avx-lowering
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
for name in legacy vex128 vex256 zero; do
 printf 'Require Import Picinae.Examples.claude.lifter.x64_copy_fixture.e26_%s_amd64.\n' "$name"
 printf 'Check Picinae.Examples.claude.lifter.x64_copy_fixture.e26_%s_amd64.welltyped.\n' "$name"
 printf 'Print Assumptions Picinae.Examples.claude.lifter.x64_copy_fixture.e26_%s_amd64.welltyped.\n' "$name"
done > "$query/Assumptions.v"
cat >> "$query/Assumptions.v" <<'EOF'
Require Import Picinae.Examples.claude.lifter.x64_copy_pinned.e26_pinned_moves_amd64.
Check Picinae.Examples.claude.lifter.x64_copy_pinned.e26_pinned_moves_amd64.welltyped.
Print Assumptions Picinae.Examples.claude.lifter.x64_copy_pinned.e26_pinned_moves_amd64.welltyped.
EOF
exec rocq compile -q -R "$state/dune-build/default" Picinae "$query/Assumptions.v"
