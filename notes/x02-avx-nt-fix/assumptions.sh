#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=13000000
export PROOF_STACK_KB=65536
ulimit -v "$PROOF_MEMORY_KB"
ulimit -s "$PROOF_STACK_KB"
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_nt_proof \
  memmove_avx_correct_nt nt_seg_1285 nt_adv4 nt_adv2 cpy_store8 \
  nt_seg_1117 nt_seg_1125 nt_seg_1210 nt_seg_1613 nt_seg_1621 nt_seg_1706
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_nt_witness \
  nt_entry_inputs_satisfiable nt_zero_memory_load
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_nt_stores \
  cpy_store16 cpy_store16_inputs_satisfiable
bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_proof \
  memmove_avx_welltyped memmove_avx_nwc memmove_avx_preserves_callee_saved
