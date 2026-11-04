#!/usr/bin/env bash
set -e
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'ulimit -v 3000000; ulimit -s 65536; export PROOF_MEMORY_KB=3000000; dune build --cache=disabled -j1 --display short Examples/claude/arm8_ffsl_proof.vo'
