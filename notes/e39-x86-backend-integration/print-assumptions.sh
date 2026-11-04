#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e39-x86-backend-integration
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
for file in Examples/claude/lifter/x64_scalar_*/*.v Examples/claude/lifter/x64_copy_*/*.v Examples/claude/lifter/x64_rep_*/*.v Examples/claude/lifter/x64_bitscan_*/*.v Examples/claude/lifter/x64_integrated_*/*.v; do
 module=${file%.v}; module=${module//\//.}
 printf 'Require Import Picinae.%s.\nCheck Picinae.%s.welltyped.\nPrint Assumptions Picinae.%s.welltyped.\n' "$module" "$module" "$module"
done > "$query/Assumptions.v"
cp "$query/Assumptions.v" notes/e39-x86-backend-integration/Assumptions.v
printf 'COMMAND=rocq compile -q -R %q Picinae %q\n' "$state/dune/default" "$query/Assumptions.v"
rocq compile -q -R "$state/dune/default" Picinae "$query/Assumptions.v"
