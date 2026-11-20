#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering
run=$(mktemp -d "$state/replay.XXXXXXXX")
python3 tools/ghidra-lifter/lift-bitscan.py --cet-disabled --out "$run/glibc" ffs ffsl ffsll
python3 tools/ghidra-lifter/lift-bitscan.py --samples --bmi1 present --out "$run/hot" hot_scans
names=()
for op in bsf bsr tzcnt lzcnt; do
  for width in 32 64; do names+=("$op$width" "${op}${width}_alias"); done
done
python3 tools/ghidra-lifter/lift-bitscan.py --fixture --bmi1 present --abm present --out "$run/fixture" "${names[@]}"
python3 tools/ghidra-lifter/lift-bitscan.py --fixture --bmi1 absent --abm absent --out "$run/fallback" tzcnt32_alias tzcnt64_alias lzcnt32_alias lzcnt64_alias
python3 - "$run" "${1:---check}" <<'PY'
from pathlib import Path
import shutil,sys
run,mode=Path(sys.argv[1]),sys.argv[2]
for source in ['glibc','hot','fixture','fallback']:
    source=run/source
    output=Path('Examples/claude/lifter')/('x64_bitscan_'+source.name)
    if mode=='--update':
        output.mkdir(exist_ok=True)
        for f in source.iterdir():shutil.copy2(f,output/f.name)
    else:
        assert mode=='--check'
        assert {f.name for f in source.iterdir()}=={f.name for f in output.iterdir() if f.suffix in ('.v','.json')}
        for f in source.iterdir():assert f.read_bytes()==(output/f.name).read_bytes(),f
print('PASS complete deterministic bit-scan artifact sets '+mode)
PY
