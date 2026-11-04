#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_memcpy_common \
  byte_of_getmem byte_setmem_cases cpy_empty cpy_equiv cpy_copied addmsub \
  cpy_load msub_add_l msub_off cpy_store
cases=()
for n in {0..32}; do cases+=("memcpy_small_case_$n"); done
bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_memcpy_small_proof \
  memcpy_small_nwc memcpy_small_welltyped memcpy_small_witness_typed \
  memcpy_small_entry_inhabited memcpy_small_zero_entry \
  memcpy_small_correct memcpy_small_preserves_callee_saved "${cases[@]}"
