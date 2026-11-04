#!/usr/bin/env bash
set -euo pipefail
export PROOF_MEMORY_KB=2000000
ulimit -v 2000000
ulimit -s 65536
query=$(mktemp -d "$PWD/_build/e36-assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
python3 - "$query/Assumptions.v" <<'PY'
from pathlib import Path
import re,sys
root=Path('Examples/claude/lifter/scalar_cneg')
text=''
for p in sorted(root.glob('*.v')):
    text += 'Require Import Picinae.Examples.claude.lifter.scalar_cneg.'+p.stem+'.\n'
    for name in re.findall(r'^Theorem (\w+)',p.read_text(),re.M):
        text += 'Check '+p.stem+'.'+name+'.\nPrint Assumptions '+p.stem+'.'+name+'.\n'
Path(sys.argv[1]).write_text(text)
print(text)
PY
rocq compile -q -R _build/default Picinae "$query/Assumptions.v"
