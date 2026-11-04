#!/usr/bin/env bash
# Run only after the complete proof target has passed. All queries are serial.
set -euo pipefail
bash tools/record-command.sh notes/a-insque/assumptions.log \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-insque --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
    ulimit -v 1750000
    ulimit -s 65536
    bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_insque_proof \
      insque_nwc insque_welltyped insque_preserves_callee_saved insque_exact \
      insque_ret_map insque_return insque_return_frame insque_halves \
      insque_lo insque_hi insque_empty_links insque_links insque_byte_frame \
      insque_mask_bound insque_witness_typed insque_witness_access \
      insque_empty_witness insque_tail_witness insque_circular_witness
  '
