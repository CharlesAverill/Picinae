#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=3000000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh \
 Picinae.Examples.claude.amd64_memmove_avx_forward_high_size_proof \
 high_welltyped high_nwc high_preserves_callee_saved \
 high_no_unsigned_backward high_sign_classification \
 high_zero_dispatch_example high_encoded_zero_branch \
 memmove_avx_correct_forward_high_size memmove_avx_forward_high_size_at_ret \
 high_witness_thresholds high_entry_satisfiable
