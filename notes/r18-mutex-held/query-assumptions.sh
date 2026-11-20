#!/usr/bin/env bash
# Run only after the full target is successfully checked; fixer handoff recipe.
set -euo pipefail
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_pvTaskIncrementMutexHeldCount_proof \
  mutex_held_nwc mutex_held_welltyped mutex_held_register_frame \
  mutex_held_null_memory mutex_held_count_increment mutex_held_memory_frame \
  mutex_held_written_bytes mutex_held_zero_bound mutex_held_entry_models \
  mutex_held_entry_satisfiable mutex_held_current_satisfiable mutex_held_correct \
  mutex_held_post_at_bx mutex_held_preserves_callee_saved \
  mutex_held_return_step mutex_held_caller_result
