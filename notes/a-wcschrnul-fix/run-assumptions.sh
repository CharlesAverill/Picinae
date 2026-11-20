#!/usr/bin/env bash
# Run only after a successful full proof build. Uses the required shared gate.
set -euo pipefail
bash tools/record-command.sh notes/a-wcschrnul-fix/assumptions.log \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-wcschrnul-fix --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
    ulimit -v 1750000
    ulimit -s 65536
    bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_wcschrnul_proof \
      wcschrnul_nwc wcschrnul_welltyped wcschrnul_preserves_memory \
      wcschrnul_preserves_callee_saved wcschrnul_stop_hit wcschrnul_stop_miss \
      wcschrnul_addr_bound wcschrnul_eq32 wcschrnul_input_satisfiable \
      wcschrnul_correct wcschrnul_return
  '
