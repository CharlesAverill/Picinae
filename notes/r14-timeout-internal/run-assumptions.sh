#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
exec bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_vTaskInternalSetTimeOutState_proof \
  timeout_nwc timeout_welltyped timeout_zero_bound timeout_witness_models \
  timeout_entry_satisfiable timeout_ranges_separate timeout_separation_nonvacuous \
  timeout_original_memory timeout_original_fields timeout_original_bytes \
  timeout_memory_frame timeout_correct timeout_post_at_bx \
  timeout_preserves_callee_saved timeout_return_step timeout_caller_result
