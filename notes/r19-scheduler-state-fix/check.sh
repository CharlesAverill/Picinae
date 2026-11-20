#!/usr/bin/env bash
set -euo pipefail
unit=notes/r19-scheduler-state-fix
mode=${1:?build, timed, clean, or assumptions}
log=${2:?log stem}
proof=Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v
cp "$proof" "$unit/$log.v.txt"
case "$mode" in
build) command='ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.vo';;
clean) command='ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.vo';;
timed) mkdir -p _build/r19-diagnostic; cp "$proof" _build/r19-diagnostic/Attempt.v
command='ulimit -s 65536; rocq compile -time -q -R _build/default Picinae _build/r19-diagnostic/Attempt.v';;
assumptions) command='ulimit -s 65536; export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536; bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_xTaskGetSchedulerState_proof scheduler_state_nwc scheduler_state_welltyped scheduler_state_preserves_memory scheduler_state_adc_result scheduler_state_zero_bound scheduler_state_witness_models scheduler_state_entry_satisfiable scheduler_state_correct scheduler_state_post_at_bx scheduler_state_preserves_callee_saved scheduler_state_original_memory scheduler_state_return_step scheduler_state_caller_result';;
*) exit 2;;
esac
bash tools/record-command.sh "$unit/$log.log" \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit r19-scheduler-state-fix --memory-kib 1750000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c "$command"
