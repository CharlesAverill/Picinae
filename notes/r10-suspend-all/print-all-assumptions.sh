#!/usr/bin/env bash
# Run only after a successful full target, inside the assigned admission gate.
set -euo pipefail
export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_vTaskSuspendAll_proof \
  suspend_all_nwc \
  suspend_all_welltyped \
  suspend_all_zero_bound \
  suspend_all_witness_models \
  suspend_all_entry_satisfiable \
  suspend_all_entry_nonempty \
  suspend_all_memory_word \
  suspend_all_memory_byte \
  suspend_all_outside_distance \
  suspend_all_memory_frame \
  suspend_all_correct \
  suspend_all_post_at_bx \
  suspend_all_original_memory_effects \
  suspend_all_preserves_callee_saved \
  suspend_all_return_step \
  suspend_all_caller_result
