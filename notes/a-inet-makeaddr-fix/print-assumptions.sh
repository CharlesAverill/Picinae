#!/usr/bin/env bash
# Run through the campaign's read-only isolated environment.
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_inet_makeaddr_proof \
  inet_makeaddr_nwc inet_makeaddr_welltyped \
  inet_makeaddr_preserves_memory inet_makeaddr_preserves_callee_saved \
  inet_makeaddr_preserves_sp inet_makeaddr_preserves_x30 inet_makeaddr_ret_map \
  inet_makeaddr_result_bound inet_rev32_correct \
  inet_bfm24_correct inet_bfm16_correct inet_bfm8_correct inet_msub32_eqb \
  inet_makeaddr_zero_typed inet_makeaddr_input_typed \
  inet_makeaddr_inputs_inhabited inet_makeaddr_spec_inhabited inet_makeaddr_correct \
  makeaddr inet_makeaddr_result inet_makeaddr_postcondition \
  inet_makeaddr_exit inet_makeaddr_invs inet_makeaddr_saved \
  inet_rev32 inet_bfm32 inet_makeaddr_input
bash tools/print-assumptions.sh \
  Picinae.Examples.claude.lifter.scalar_bitforms.e29_inet_makeaddr_arm8 welltyped
