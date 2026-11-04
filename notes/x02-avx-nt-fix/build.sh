#!/usr/bin/env bash
set -euo pipefail
ulimit -v 13000000
ulimit -s 65536
export PROOF_MEMORY_KB=13000000
export PROOF_STACK_KB=65536
dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_nt_proof.vo Examples/claude/amd64_memmove_avx_nt_witness.vo
