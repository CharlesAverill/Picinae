#!/usr/bin/env bash
set -euo pipefail
ulimit -v 4000000
ulimit -s 65536
dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.vo
