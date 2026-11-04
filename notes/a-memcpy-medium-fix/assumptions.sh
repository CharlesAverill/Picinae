#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=3000000 PROOF_STACK_KB=65536
ulimit -v 3000000
ulimit -s 65536
mapfile -t facts < <(sed -nE 's/^(Theorem|Lemma) ([a-zA-Z0-9_]+):.*/\2/p' Examples/claude/arm8_memcpy_medium_proof.v)
bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_memcpy_medium_proof "${facts[@]}"
bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_memcpy_common byte_of_getmem byte_setmem_cases cpy_empty cpy_equiv cpy_copied addmsub cpy_load msub_add_l msub_off cpy_store
