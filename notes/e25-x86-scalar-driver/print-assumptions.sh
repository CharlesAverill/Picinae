#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000
query=$(mktemp -d "$PWD/_build/e25-assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
for name in toascii isascii abs labs pthread_equal; do
  printf 'Require Import Picinae.Examples.claude.lifter.x64_scalar_smoke.e25_%s_amd64.\n' "$name"
  printf 'Check Picinae.Examples.claude.lifter.x64_scalar_smoke.e25_%s_amd64.welltyped.\n' "$name"
  printf 'Print Assumptions Picinae.Examples.claude.lifter.x64_scalar_smoke.e25_%s_amd64.welltyped.\n' "$name"
done > "$query/Assumptions.v"
for name in scalar_caller scalar_callee; do
  printf 'Require Import Picinae.Examples.claude.lifter.x64_scalar_fixture.e25_%s_amd64.\n' "$name"
  printf 'Check Picinae.Examples.claude.lifter.x64_scalar_fixture.e25_%s_amd64.welltyped.\n' "$name"
  printf 'Print Assumptions Picinae.Examples.claude.lifter.x64_scalar_fixture.e25_%s_amd64.welltyped.\n' "$name"
done >> "$query/Assumptions.v"
rocq compile -q -R _build/default Picinae "$query/Assumptions.v"
