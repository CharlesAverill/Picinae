#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=6000000 PROOF_STACK_KB=65536
ulimit -v 6000000
ulimit -s 65536
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_overlap_forward_proof \
 ofw_welltyped ofw_nwc ofw_preserves_callee_saved ofw_load ofw_store4 \
 lor31 a0_bounds getmem_addr ja_not_taken ja_taken msub_add_mod \
 ofw_dispatch ofw_heuristic_nonzero \
 memmove_avx_correct_overlap_forward memmove_avx_overlap_forward_at_ret \
 ofw_witness_thresholds ofw_entry_satisfiable ofw_critical_distances
