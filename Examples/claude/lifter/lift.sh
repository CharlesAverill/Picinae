#!/bin/sh
# Lift functions from the Ghidra project built from the system libc.
#   ./lift.sh <func>[=<coqname>] ...
# Output goes to Examples/claude/.  Requires the Ghidra flatpak (with PyGhidra
# installed in its venv) and a pcode2coq checkout at $P2C.
HERE=$(cd "$(dirname "$0")" && pwd)
P2C=${P2C:-$HOME/Desktop/pcode2coq}
PROJ=${PROJ:-$HOME/.cache/picinae_lift/proj}
flatpak run --command=/app/lib/ghidra/support/pyghidraRun org.ghidra_sre.Ghidra -H \
  "$PROJ" libc -process libc.so.6 -noanalysis -readOnly \
  -scriptPath "$HERE" -postScript pcode2coq_headless.py "$P2C" "$HERE/.." "$@" \
  < /dev/null > "$HERE/last_lift.log" 2>&1
grep -E 'pcode2coq_headless|Traceback|Error' "$HERE/last_lift.log"
