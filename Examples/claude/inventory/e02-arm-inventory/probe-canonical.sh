#!/usr/bin/env bash
# A diagnostic only: the unmodified original driver must reject this library.
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
REPO=$(cd -- "$HERE/../../../.." && pwd)
UNIT_TC=/home/charles/code/friends/.toolchains/e02-arm-inventory
export JAVA_HOME="$UNIT_TC/jdk-21.0.8+9" GHIDRA_INSTALL_DIR="$UNIT_TC/ghidra_11.4.2_PUBLIC"
export PATH="$UNIT_TC/venv/bin:$JAVA_HOME/bin:$PATH"
export XDG_CONFIG_HOME="$UNIT_TC/config" XDG_CACHE_HOME="$UNIT_TC/cache" TMPDIR="$UNIT_TC/tmp" PYTHONDONTWRITEBYTECODE=1
export JAVA_TOOL_OPTIONS="-Xmx2G -Duser.home=$UNIT_TC/config -Djava.io.tmpdir=$UNIT_TC/tmp"
rm -f "$UNIT_TC/canonical-probe/e02_original.v"
python -m pyghidra --skip-analysis --project-path "$UNIT_TC/projects" --project-name e02-audit \
  "$UNIT_TC/root/lib/aarch64-linux-gnu/libc.so.6" "$REPO/Examples/claude/lifter/pcode2coq_headless.py" \
  "$REPO/tools/ghidra-lifter" "$UNIT_TC/canonical-probe" toascii=e02_original \
  > "$HERE/evidence/canonical-driver-compatibility.log" 2>&1
test ! -e "$UNIT_TC/canonical-probe/e02_original.v"
rg -q "FAILED toascii: 'LiftInfo' object has no attribute 'prependProgName'" \
  "$HERE/evidence/canonical-driver-compatibility.log"
printf 'PASS expected compatibility rejection; original driver launcher exit=0 despite failure\n'
