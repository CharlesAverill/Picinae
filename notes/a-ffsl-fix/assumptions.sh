#!/usr/bin/env bash
set -eu
export PROOF_MEMORY_KB=3000000
export PROOF_STACK_KB=65536
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash tools/print-assumptions.sh \
  Picinae.Examples.claude.arm8_ffsl_proof \
  ffsl_correct ffsll_correct \
  ffsl_nwc ffsl_welltyped ffsl_ffsll_program_identity \
  ffsl_preserves_memory ffsl_preserves_callee_saved ffsl_entry_satisfiable \
  ffsl_lowest_set_bit ffsl_spec_satisfiable rbit32_bound rbit32_bits \
  ffsl_clz_rbit ffsl_asr_upper ffsl_isolate ffsl_value_spec \
  ffsl_rbit_size ffsl_count_result ffsl_branch
