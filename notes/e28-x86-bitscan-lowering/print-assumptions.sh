#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000
state=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
for file in Examples/claude/lifter/x64_bitscan_*/*.v Examples/claude/lifter/x64_scalar_*/*.v; do
  module=${file%.v}; module=${module//\//.}
  printf 'Require Import Picinae.%s.\nCheck Picinae.%s.welltyped.\nPrint Assumptions Picinae.%s.welltyped.\n' "$module" "$module" "$module"
done > "$query/Assumptions.v"
rocq compile -q -R "$state/dune/default" Picinae "$query/Assumptions.v"
