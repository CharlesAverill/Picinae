#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering
run=$(mktemp -d "$state/e25-replay.XXXXXXXX")
python3 tools/ghidra-lifter/lift-x64.py --state "$state" --cet-disabled --out "$run/glibc" toascii isascii abs labs pthread_equal
python3 tools/ghidra-lifter/lift-x64.py --state "$state" --fixture --out "$run/fixture" scalar_caller scalar_callee
python3 - "$run" <<'PY'
from pathlib import Path
import sys
run=Path(sys.argv[1])
for source,dest in [('glibc','x64_scalar_smoke'),('fixture','x64_scalar_fixture')]:
    for p in (run/source).iterdir():
        if p.name=='SUCCESS.json':continue # receipt implementation hash changed, IL/pcode did not
        assert p.read_bytes()==(Path('Examples/claude/lifter')/dest/p.name).read_bytes(),p
print('PASS seven preserved e25 IL and raw-pcode artifact pairs reproduce byte-for-byte')
PY
