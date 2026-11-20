#!/usr/bin/env bash
set -euo pipefail
mapfile -t facts < <(sed -nE 's/^(Theorem|Lemma) ([A-Za-z_][A-Za-z_0-9]*).*/\2/p' Examples/FreeRTOSMask/armv6m_port_mask_proof.v)
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c '
  ulimit -v 2000000
  ulimit -s 65536
  exec bash tools/print-assumptions.sh Picinae.Examples.FreeRTOSMask.armv6m_port_mask_proof "$@"
' bash "${facts[@]}"
