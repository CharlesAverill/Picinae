#!/usr/bin/env bash
set -euo pipefail
log=${1:?log basename required}
bash tools/record-command.sh "notes/a-wcschrnul-fix/$log.log" \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-wcschrnul-fix --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_wcschrnul_proof.vo'
