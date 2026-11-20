#!/usr/bin/env bash
# Run only after a successful full target; always use the shared admission gate.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec bash tools/record-command.sh notes/a-ffs/assumptions.log \
 python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit a-ffs --memory-kib 1750000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c '
 export PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536
 bash tools/print-assumptions.sh Picinae.Examples.claude.arm8_ffs_proof \
 ffs_nwc ffs_welltyped ffs_preserves_memory ffs_preserves_callee_saved \
 ffs_return_cut ffs_lowest_set_bit ffs_isolate ffs_spec_satisfiable \
 ffs_isolation_spec ffs_table_bytes_correct ffs_table_satisfiable \
 ffs_table_memory_bound ffs_entry_satisfiable ffs_correct \
 ffs_return_guard_satisfiable ffs_guarded_return
 '
