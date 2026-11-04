#!/usr/bin/env bash
# Invoke only after the restored proof builds; all proof processes share one gate.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
bash tools/record-command.sh notes/r07-current-task-fix/assumptions.log \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r07-current-task-fix --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    ulimit -v 1750000
    ulimit -s 65536
    PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536 bash tools/print-assumptions.sh \
      Picinae.Examples.FreeRTOS.armv6m_xTaskGetCurrentTaskHandle_proof \
      current_task_nwc current_task_welltyped current_task_preserves_memory \
      current_task_zero_bound current_task_witness_models \
      current_task_entry_satisfiable current_task_entry_nonempty \
      current_task_correct current_task_post_at_bx current_task_preserves_callee_saved \
      current_task_return_step current_task_caller_result current_task_original_bytes
  '
bash tools/record-command.sh notes/r07-current-task-fix/source-audit.log \
  python3 tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006
bash tools/record-command.sh notes/r07-current-task-fix/unit-source-audit.log \
  python3 tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006 \
  Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v \
  Examples/FreeRTOS/xTaskGetCurrentTaskHandle_armv6m.v
bash tools/record-command.sh notes/r07-current-task-fix/declaration-assumption-audit.log \
  python3 notes/r07-current-task-fix/audit-declarations.py
bash tools/record-command.sh notes/r07-current-task-fix/ancestry-final.log \
  python3 notes/r07-current-task-fix/audit-ancestry.py
