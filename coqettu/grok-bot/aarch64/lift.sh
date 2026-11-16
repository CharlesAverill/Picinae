#!/usr/bin/env bash
# Lift functions from musl aarch64 libc into lifted_raw/ (Grok Bot / coqettu).
# Usage: ./lift.sh '^(strlen|memcmp)$'
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# Uses our patched copy of picinae-llm/tools/ghidra-lifter in ./lifter (see lifter/README_GROK.md)
"${GHIDRA_INSTALL_DIR:-$HOME/research/programs/ghidra_12.0_PUBLIC}/support/pyghidraRun" --headless \
  "$here/ghidra" musl_aarch64 \
  -process ld-musl-aarch64.so.1 -readOnly -noanalysis \
  -scriptPath "$here/lifter" \
  -postScript pcode2coq_headless.py \
    --functionRegex "$1" --typeCheck --globalAddressing \
    --outputDir "${OUTDIR:-$here/lifted_raw}"
