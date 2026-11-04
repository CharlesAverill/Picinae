#!/usr/bin/env bash
set -euo pipefail
git add dune Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v notes/r19-scheduler-state
# Raw evidence logs retain the original source lines, including trailing spaces.
git diff --cached --check -- dune Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v notes/r19-scheduler-state/README.md notes/r19-scheduler-state/*.py notes/r19-scheduler-state/*.sh
git commit -m "Add partial ARMv6-M scheduler state proof handoff"
