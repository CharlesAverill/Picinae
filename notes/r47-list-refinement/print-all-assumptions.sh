#!/usr/bin/env bash
# Run only after the new fixer has successfully checked the full target.
set -euo pipefail
ulimit -v 4000000
ulimit -s 65536
export PROOF_MEMORY_KB=4000000 PROOF_STACK_KB=65536
export XDG_CACHE_HOME=/home/charles/code/friends/.toolchains/r47-list-refinement/cache
export TMPDIR=/home/charles/code/friends/.toolchains/r47-list-refinement/tmp
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_list_refinement \
  ring_last_app \
  ring_last_member \
  ring_hd_member \
  ring_count_insert \
  ring_count_remove \
  ring_members_insert \
  ring_members_remove \
  ring_nodup_insert \
  ring_regions_separate \
  ring_object_fields_separate \
  ring_fresh_geometry \
  ring_permission_word \
  ring_insert_links \
  ring_remove_original \
  ring_insert_layout \
  ring_remove_layout \
  ring_insert_pre \
  ring_remove_pre \
  ring_insert_memory \
  ring_remove_memory \
  ring_insert_frame \
  ring_remove_frame \
  ring_insert_refines \
  ring_remove_refines \
  ring_empty_witness \
  ring_singleton_witness \
  ring_multi_witness \
  ring_empty_insert_witness \
  ring_singleton_remove_witness \
  ring_multi_remove_witness
