#!/usr/bin/env bash
# Shared dependencies read-only, all mutable project/JVM state confined to e26.
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e26-x86-sse-avx-lowering
run=$(mktemp -d "$state/replays/final.XXXXXXXX")
python3 tools/ghidra-lifter/lift-x64-copy.py --fixture --out "$run/synthetic" legacy vex128 vex256 zero
python3 tools/ghidra-lifter/lift-x64-copy.py --instructions --out "$run/actual" pinned_moves
python3 - "$run" "${1:---check}" <<'PY'
from pathlib import Path
import shutil,sys
run,mode=Path(sys.argv[1]),sys.argv[2]
for src,dest in [('synthetic','x64_copy_fixture'),('actual','x64_copy_pinned')]:
    source=run/src;output=Path('Examples/claude/lifter')/dest
    if mode=='--update':
        output.mkdir(exist_ok=True)
        for f in source.iterdir():shutil.copy2(f,output/f.name)
    elif mode=='--check':
        assert {f.name for f in source.iterdir()}=={f.name for f in output.iterdir() if f.suffix in ('.v','.json')}
        for f in source.iterdir():assert f.read_bytes()==(output/f.name).read_bytes(),f
    else:raise ValueError('expected --check or --update')
print('PASS five complete deterministic artifact sets ('+mode+')')
PY
