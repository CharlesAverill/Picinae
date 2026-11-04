#!/usr/bin/env bash
# No installation. Reuse only the pinned e02 toolchain read-only.
set -euo pipefail
repo=$(cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$repo"
state=/home/charles/code/friends/.toolchains/e11-canonical-lifter
# The caller supplies a NEW run name; existing output is deliberately rejected.
run=${1:?Usage: reproduce.sh NEW_RUN_NAME}
[[ $run =~ ^[A-Za-z0-9_-]+$ ]]
python3 tools/ghidra-lifter/lift-scalar.py --out "$state/$run-scalar" toascii div ldiv swab ffs ffsl
python3 tools/ghidra-lifter/lift-scalar.py --global-addressing --out "$state/$run-global" mempcpy __memcpy_generic
python3 - "$state" "$run" <<'PY'
from pathlib import Path
import shutil, sys
state, run = Path(sys.argv[1]), sys.argv[2]
for kind, dest in [('scalar','scalar_smoke'),('global','scalar_global')]:
    for f in (state/f'{run}-{kind}').iterdir():
        shutil.copy2(f,Path('Examples/claude/lifter')/dest/f.name)
PY
# Only bounded full-vo kernel checking; no .vos or shared cache.
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c '
  ulimit -v 3000000
  ulimit -s 65536
  dune build --cache=disabled -j1 --display short @scalar-lifter
'
