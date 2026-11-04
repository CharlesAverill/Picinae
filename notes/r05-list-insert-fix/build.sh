#!/usr/bin/env bash
set -euo pipefail
bash tools/record-command.sh "notes/r05-list-insert-fix/$1.log" \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit r05-list-insert-fix --memory-kib 2500000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c 'ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInsert_proof.vo'
