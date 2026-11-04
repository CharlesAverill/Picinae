#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
dune build --cache=disabled -j1 --display short --no-buffer Examples/claude/arm8_memcpy_small_proof.vo
