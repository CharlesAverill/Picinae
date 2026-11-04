#!/usr/bin/env bash
set -eu
exec bash tools/record-command.sh "notes/x07-avx-rep-overlap-fix/$1.log" \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit x07-avx-rep-overlap-fix --memory-kib 6000000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'export PROOF_MEMORY_KB=6000000 PROOF_STACK_KB=65536
 bash tools/print-assumptions.sh Picinae.Examples.claude.amd64_memmove_avx_rep_overlap_proof \
 orp_welltyped orp_nwc orp_preserves_callee_saved orp_neg_distance \
 memmove_avx_correct_rep_overlap memmove_avx_rep_overlap_at_ret \
 orp_witness_globals orp_entry_satisfiable orp_critical_distances'
