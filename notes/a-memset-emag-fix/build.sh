#!/usr/bin/env bash
set -eu
bash tools/record-command.sh "notes/a-memset-emag-fix/$1.log" \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit a-memset-emag-fix --memory-kib 3000000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c 'ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_memset_emag_proof.vo'
