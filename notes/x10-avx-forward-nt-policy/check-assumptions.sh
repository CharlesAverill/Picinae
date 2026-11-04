#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=4000000 PROOF_STACK_KB=65536
ulimit -v "$PROOF_MEMORY_KB"
ulimit -s "$PROOF_STACK_KB"
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_forward_nt_policy_proof \
  ofnt_welltyped ofnt_nwc ofnt_preserves_callee_saved \
  ofnt_reverse_gap ofnt_negative_gap \
  memmove_avx_correct_forward_nt_policy memmove_avx_forward_nt_policy_at_ret \
  ofnt_witness_thresholds ofnt_entry_satisfiable ofnt_critical_distances
