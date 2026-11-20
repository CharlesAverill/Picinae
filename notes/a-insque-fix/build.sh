#!/usr/bin/env bash
set -euo pipefail
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py --unit a-insque-fix --memory-kib 1750000 -- /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c '
  ulimit -v 1750000
  ulimit -s 65536
  dune build --cache=disabled -j1 --display short Examples/claude/arm8_insque_proof.vo
'
