#!/usr/bin/env bash
set -euo pipefail
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c '
 ulimit -v 8000000
 ulimit -s 65536
 /usr/bin/time -v dune build --no-buffer --cache=disabled -j1 --display short Examples/claude/amd64_memcpy_nt_strategy_proof.vo
'
