#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536
bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_vListInsertEnd_proof \
  insert_end_nwc \
  insert_end_welltyped \
  insert_end_preserved \
  insert_end_register_frame \
  insert_apart_from \
  insert_separate_words \
  insert_end_words \
  insert_end_layout \
  insert_end_links \
  insert_end_ordinary_lr \
  insert_end_writes \
  insert_end_permissions \
  insert_end_pre \
  insert_end_prefix \
  insert_end_memory \
  insert_end_byte_frame \
  insert_end_fields \
  insert_end_observed_B \
  insert_end_observed_prefix \
  insert_end_observed_count \
  insert_end_observed_memory \
  insert_end_flags \
  insert_end_exact_post \
  insert_end_post \
  insert_end_exit \
  insert_end_invs \
  insert_end_memory_fields \
  insert_end_memory_frame \
  insert_end_original_loads \
  insert_end_exact \
  insert_end_at_bx \
  insert_end_count_no_overflow \
  insert_end_fixture \
  insert_end_fixture_links \
  insert_end_fixture_typed \
  insert_end_entry_store \
  insert_end_entry_witness \
  insert_end_empty_layout \
  insert_end_nonempty_layout \
  insert_end_local_empty_witness \
  insert_end_local_nonempty_witness \
  insert_end_return_step \
  insert_end_trace_returns \
  insert_end_ordinary_return_nonvacuity
