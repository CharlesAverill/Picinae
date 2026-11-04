#!/usr/bin/env bash
set -eu
export PROOF_MEMORY_KB=6000000 PROOF_STACK_KB=65536
ulimit -v 6000000
ulimit -s 65536
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash tools/print-assumptions.sh \
 Picinae.Examples.claude.amd64_memmove_avx_rep_overlap_proof \
 orp_welltyped orp_nwc orp_preserves_callee_saved orp_neg_distance \
 memmove_avx_correct_rep_overlap memmove_avx_rep_overlap_at_ret \
 orp_witness_globals orp_entry_satisfiable orp_critical_distances
