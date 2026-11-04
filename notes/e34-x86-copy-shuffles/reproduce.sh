#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
state=/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles
run=$(mktemp -d "$state/replays/reproduce.XXXXXXXX")
python3 tools/ghidra-lifter/lift-x64-shuffle.py --fixture --out "$run/synthetic" align
python3 tools/ghidra-lifter/lift-x64-shuffle.py --instructions --out "$run/actual" pinned_shuffles
python3 - "$run" "${1:---check}" <<'PY'
from pathlib import Path
import shutil,sys
run,mode=Path(sys.argv[1]),sys.argv[2]
for src,dest in [('synthetic','x64_shuffle_fixture'),('actual','x64_shuffle_pinned')]:
    source=run/src;output=Path('Examples/claude/lifter')/dest
    if mode=='--update':
        output.mkdir(exist_ok=True)
        for f in source.iterdir():shutil.copy2(f,output/f.name)
    elif mode=='--check':
        assert {f.name for f in source.iterdir()}=={f.name for f in output.iterdir()}
        for f in source.iterdir():assert f.read_bytes()==(output/f.name).read_bytes(),f
    else:raise ValueError('expected --check or --update')
print('PASS two deterministic artifacts ('+mode+')')
PY
