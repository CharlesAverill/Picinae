#!/bin/bash
set -eu
bash tools/record-command.sh "notes/r47-list-refinement-fix/$1-build.log" \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r47-list-refinement-fix --memory-kib 3000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -s 65536; /usr/bin/time -v dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_list_refinement.vo'
