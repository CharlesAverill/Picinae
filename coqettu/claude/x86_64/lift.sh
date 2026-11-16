#!/bin/sh
# Lift functions from musl x86_64 (Alpine musl-1.2.6-r6) with global addressing.
#   ./lift.sh '<python regex over function names>'
# The Ghidra project coqettu_claude holds libc.musl-x86_64.so.1, imported
# under the name of its (byte-identical) symlink target ld-musl-x86_64.so.1;
# sha256 cc3e0200...4714647.  Ghidra image base 0x100000.
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
mkdir -p "$HERE/programs" "$HERE/logs"
"$GHIDRA_INSTALL_DIR/support/pyghidraRun" --headless "$HOME/research/ghidra_projects" coqettu_claude \
  -process ld-musl-x86_64.so.1 -noanalysis -readOnly \
  -scriptPath "$ROOT/tools/ghidra-lifter" -postScript pcode2coq_headless.py \
  --functionRegex "$1" --typeCheck --globalAddressing --outputDir "${OUT:-$HERE/programs}" \
  < /dev/null > "$HERE/logs/last_lift.log" 2>&1
grep -E 'pcode2coq|Traceback|Error|ERROR|WARN.*pcode' "$HERE/logs/last_lift.log" | grep -v '^INFO' | head -40
