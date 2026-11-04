#!/usr/bin/env bash
# Run only after the assigned full target succeeds. No installation.
set -euo pipefail
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-memcpy-large --memory-kib 4000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    export PROOF_MEMORY_KB=4000000 PROOF_STACK_KB=65536
    ulimit -v 4000000
    ulimit -s 65536
    bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_memcpy_large_proof \
      memcpy_large_nwc memcpy_large_welltyped memcpy_large_separated \
      memcpy_large_size_bound memcpy_large_nov_of_separated \
      memcpy_large_witness_typed memcpy_large_entry_inhabited \
      memcpy_large_zero_source_entry memcpy_large_wrapped_end_entry \
      memcpy_large_written_bound memcpy_large_written_advance \
      memcpy_large_tail_cover memcpy_large_source_unchanged \
      memcpy_large_store_value memcpy_large_entry_step memcpy_large_head_step \
      memcpy_large_loop_step memcpy_large_tail_step memcpy_large_correct \
      memcpy_large_returns_original_bytes memcpy_large_preserves_callee_saved
  '
