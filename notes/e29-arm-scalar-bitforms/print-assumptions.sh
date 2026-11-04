#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=2000000
ulimit -v 2000000
ulimit -s 65536
query=$(mktemp -d "$PWD/_build/e29-assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
cat > "$query/Assumptions.v" <<'EOF'
Require Import Picinae.Examples.claude.lifter.scalar_bitforms.e29_bitforms.
Check e29_bitforms.welltyped.
Print Assumptions e29_bitforms.welltyped.
Check e29_bitforms.finite_execution.
Print Assumptions e29_bitforms.finite_execution.
Require Import Picinae.Examples.claude.lifter.scalar_bitforms.e29_inet_makeaddr_arm8.
Check e29_inet_makeaddr_arm8.welltyped.
Print Assumptions e29_inet_makeaddr_arm8.welltyped.
Require Import Picinae.Examples.claude.lifter.scalar_bitforms.e29_rand_r_arm8.
Check e29_rand_r_arm8.welltyped.
Print Assumptions e29_rand_r_arm8.welltyped.
EOF
rocq compile -q -R _build/default Picinae "$query/Assumptions.v"
