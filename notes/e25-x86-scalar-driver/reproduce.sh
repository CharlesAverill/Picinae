#!/usr/bin/env bash
# No installs. All shared dependencies read-only; one JVM/compiler phase at a time.
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e25-x86-scalar-driver
run=$(mktemp -d "$state/replay.XXXXXXXX")
python3 tools/ghidra-lifter/lift-x64.py --cet-disabled --out "$run/glibc" toascii isascii abs labs pthread_equal
python3 tools/ghidra-lifter/lift-x64.py --fixture --out "$run/synthetic" scalar_caller scalar_callee
python3 - "$run" "${1:---check}" <<'PY'
from pathlib import Path
import shutil,sys
run,mode=Path(sys.argv[1]),sys.argv[2]
for src,dest in [('glibc','x64_scalar_smoke'),('synthetic','x64_scalar_fixture')]:
    source=run/src
    output=Path('Examples/claude/lifter')/dest
    if mode=='--update':
        output.mkdir(exist_ok=True)
        for f in source.iterdir(): shutil.copy2(f,output/f.name)
    elif mode=='--check':
        assert {f.name for f in source.iterdir()}=={f.name for f in output.iterdir() if f.suffix in ('.v','.json')}
        for f in source.iterdir(): assert f.read_bytes()==(output/f.name).read_bytes(),f
    else: raise ValueError('expected --check or --update')
print('PASS complete deterministic artifact sets ('+mode+')')
PY
