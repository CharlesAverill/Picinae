#!/usr/bin/env bash
set -eu
exec bash tools/record-command.sh notes/x07-avx-rep-overlap/10-initial-full-vo.log \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 6000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_rep_overlap_proof.vo Examples/claude/amd64_memmove_avx_rep_proof.vo'
