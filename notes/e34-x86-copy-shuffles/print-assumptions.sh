#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles
query=$(mktemp -d "$state/assumptions.XXXXXXXX")
python3 - > "$query/Assumptions.v" <<'PY'
from pathlib import Path
import re
text=Path('dune').read_text()
modules=sorted(set(re.findall(r'Examples\.claude\.lifter\.[A-Za-z_0-9.]+',text)))
for m in modules:
    print('Require Import Picinae.'+m+'.')
    print('Check Picinae.'+m+'.welltyped.')
    print('Print Assumptions Picinae.'+m+'.welltyped.')
PY
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env rocq compile -q -R "$state/dune-build/default" Picinae "$query/Assumptions.v"
