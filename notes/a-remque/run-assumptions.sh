#!/usr/bin/env bash
# Run only after a successful full target build; not executed after Astra failure.
set -euo pipefail
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-remque --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
    bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_remque_proof \
      remque_nwc remque_welltyped remque_preserves_callee_saved \
      remque_exact remque_correct remque_byte_frame remque_post_byte_frame \
      remque_ret_exec remque_path_empty remque_path_next_only \
      remque_path_prev_only remque_path_both remque_witness_fields \
      remque_witness_typed remque_arbitrary_witness remque_empty_witness \
      remque_singleton_witness remque_shared_sentinel_witness \
      remque_nonempty_witness remque_next_only_witness remque_prev_only_witness
  '
