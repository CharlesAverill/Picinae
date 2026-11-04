#!/usr/bin/env bash
set -euo pipefail
# Run this only after a successful complete initial build (or by the Sol fixer).
# The outer resource gate enforces the same hard cap for the entire process tree.
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r19-scheduler-state --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    ulimit -v 1750000
    ulimit -s 65536
    export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
    bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_xTaskGetSchedulerState_proof \
      scheduler_state_nwc scheduler_state_welltyped scheduler_state_preserves_memory \
      scheduler_state_adc_result scheduler_state_zero_bound scheduler_state_witness_models \
      scheduler_state_entry_satisfiable scheduler_state_correct scheduler_state_post_at_bx \
      scheduler_state_preserves_callee_saved scheduler_state_original_memory \
      scheduler_state_return_step scheduler_state_caller_result
  '
