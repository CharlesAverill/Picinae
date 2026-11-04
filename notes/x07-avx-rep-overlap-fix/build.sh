#!/usr/bin/env bash
set -eu
exec bash tools/record-command.sh "notes/x07-avx-rep-overlap-fix/$1.log" \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit x07-avx-rep-overlap-fix --memory-kib 6000000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 6000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short --no-buffer Examples/claude/amd64_memmove_avx_rep_overlap_proof.vo Examples/claude/amd64_memmove_avx_rep_proof.vo'
