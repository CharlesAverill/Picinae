#!/usr/bin/env bash
# Invoke only underneath the assigned resource-run.py gate and toolchain wrapper.
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
dune clean
bash tools/record-command.sh notes/r11-missed-yield-fix/build-clean.log \
  dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.vo
PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536 \
  bash tools/record-command.sh notes/r11-missed-yield-fix/assumptions.log \
  bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_vTaskMissedYield_proof \
  missed_yield_welltyped \
  missed_yield_nwc \
  missed_yield_memory_word \
  missed_yield_memory_bytes \
  missed_yield_memory_outside \
  missed_yield_preserves_registers \
  missed_yield_correct \
  missed_yield_post_at_bx \
  missed_yield_functional \
  missed_yield_preserves_callee_saved \
  missed_yield_zero_bound \
  missed_yield_entry_satisfiable \
  missed_yield_ldr_step \
  missed_yield_mov_step \
  missed_yield_store_step \
  missed_yield_execution_witness \
  missed_yield_return_step \
  missed_yield_execution_returns
