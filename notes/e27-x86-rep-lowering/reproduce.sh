#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e27-x86-rep-lowering
run=$(mktemp -d "$state/replay.XXXXXXXX")
export PYTHONDONTWRITEBYTECODE=1
python3 tools/ghidra-lifter/lift-x64-rep.py --out "$run/pinned"
python3 tools/ghidra-lifter/lift-x64-rep.py --fixture --out "$run/synthetic"
python3 - "$run" "${1:---check}" <<'PY'
from pathlib import Path
import shutil,sys
run,mode=Path(sys.argv[1]),sys.argv[2]
for kind in ('pinned','synthetic'):
    source=run/kind;output=Path('Examples/claude/lifter')/('x64_rep_'+kind)
    if mode=='--update':
        output.mkdir(exist_ok=True)
        for f in source.iterdir():shutil.copy2(f,output/f.name)
    elif mode=='--check':
        assert {f.name for f in source.iterdir()}=={f.name for f in output.iterdir()}
        for f in source.iterdir():assert f.read_bytes()==(output/f.name).read_bytes(),f
    else:raise ValueError('expected --check or --update')
print('PASS complete deterministic REP artifact sets '+mode)
PY
