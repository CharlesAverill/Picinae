#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e27-x86-rep-lowering
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
for kind in pinned synthetic; do
  printf 'Require Import Picinae.Examples.claude.lifter.x64_rep_%s.e27_rep_amd64.\n' "$kind"
  printf 'Check Picinae.Examples.claude.lifter.x64_rep_%s.e27_rep_amd64.welltyped.\n' "$kind"
  printf 'Print Assumptions Picinae.Examples.claude.lifter.x64_rep_%s.e27_rep_amd64.welltyped.\n' "$kind"
done > "$query/Assumptions.v"
rocq compile -q -R "$state/build/default" Picinae "$query/Assumptions.v"
