#!/usr/bin/env bash
# Run with the read-only Picinae environment wrapper, from the repo root.
set -euo pipefail
ulimit -v 3000000
ulimit -s 65536
query=$(mktemp -d "$PWD/_build/e11-assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
for n in toascii div ldiv swab ffs ffsl; do
  printf 'Require Import Picinae.Examples.claude.lifter.scalar_smoke.e11_%s_arm8.\n' "$n"
  printf 'Check Picinae.Examples.claude.lifter.scalar_smoke.e11_%s_arm8.welltyped.\n' "$n"
  printf 'Print Assumptions Picinae.Examples.claude.lifter.scalar_smoke.e11_%s_arm8.welltyped.\n' "$n"
done > "$query/Assumptions.v"
for n in mempcpy __memcpy_generic; do
  printf 'Require Import Picinae.Examples.claude.lifter.scalar_global.e11_%s_arm8.\n' "$n"
  printf 'Check Picinae.Examples.claude.lifter.scalar_global.e11_%s_arm8.welltyped.\n' "$n"
  printf 'Print Assumptions Picinae.Examples.claude.lifter.scalar_global.e11_%s_arm8.welltyped.\n' "$n"
done >> "$query/Assumptions.v"
rocq compile -q -R _build/default Picinae "$query/Assumptions.v"
