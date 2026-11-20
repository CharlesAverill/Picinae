#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=2000000
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e10-arm-neon-lifts
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
python3 - "$query/Assumptions.v" <<'PY'
from pathlib import Path
import re,sys
p=Path('Examples/claude/lifter/neon_loads/e10_neon_loads.v')
text='Require Import Picinae.Examples.claude.lifter.neon_loads.e10_neon_loads.\n'
for name in re.findall(r'^Theorem (\w+)',p.read_text(),re.M):
 text+='Check e10_neon_loads.'+name+'.\nPrint Assumptions e10_neon_loads.'+name+'.\n'
Path(sys.argv[1]).write_text(text)
print(text)
PY
rocq compile -q -R "$state/build/default" Picinae "$query/Assumptions.v"
