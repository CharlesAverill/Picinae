#!/usr/bin/env bash
# Decode exact historical instructions and emit ONLY the restricted smoke lift.
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
REPO=$(cd -- "$HERE/../../../.." && pwd)
UNIT_TC=${UNIT_TC:-/home/charles/code/friends/.toolchains/e02-arm-inventory}
OUT=${1:-"$HERE/evidence"}
mkdir -p "$UNIT_TC"/{config,cache,tmp,projects,logs} "$OUT"
export JAVA_HOME="$UNIT_TC/jdk-21.0.8+9"
export PATH="$UNIT_TC/venv/bin:$JAVA_HOME/bin:$PATH"
export GHIDRA_INSTALL_DIR="$UNIT_TC/ghidra_11.4.2_PUBLIC"
export XDG_CONFIG_HOME="$UNIT_TC/config" XDG_CACHE_HOME="$UNIT_TC/cache"
export TMPDIR="$UNIT_TC/tmp" PYTHONDONTWRITEBYTECODE=1
export JAVA_TOOL_OPTIONS="-Xmx2G -Duser.home=$UNIT_TC/config -Djava.io.tmpdir=$UNIT_TC/tmp"
# PyGhidra's Python CLI differs from support/pyghidraRun -H.  Use its actual
# pinned 2.2.1 CLI. No old project, full autoanalysis or target execution needed.
rm -f "$OUT/e02_toascii_smoke.v" "$OUT/ghidra-audit.json"
python -m pyghidra --skip-analysis --project-path "$UNIT_TC/projects" \
  --project-name e02-audit "$UNIT_TC/root/lib/aarch64-linux-gnu/libc.so.6" \
  "$HERE/ghidra_audit.py" "$REPO" "$OUT" > "$OUT/ghidra-audit.log" 2>&1
# Ghidra script errors can be logged without a nonzero launcher exit.
test -s "$OUT/e02_toascii_smoke.v"
python - "$OUT" <<'PY'
import json, pathlib, sys
rows = json.loads((pathlib.Path(sys.argv[1])/'ghidra-audit.json').read_text())
assert len(rows) == 85 and all(r['match'] for r in rows)
print('PASS 85 exact instruction comments and restricted smoke artifact')
PY
