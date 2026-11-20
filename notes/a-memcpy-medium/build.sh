#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
exec dune build --cache=disabled -j1 --display short Examples/claude/arm8_memcpy_medium_proof.vo
