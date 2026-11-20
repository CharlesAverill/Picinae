#!/usr/bin/env bash
set -eu
bash tools/record-command.sh "notes/x03-avx-overlap-forward-fix/$1.log" \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 6000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_overlap_forward_proof.vo'
