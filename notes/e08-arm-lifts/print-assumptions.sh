#!/usr/bin/env bash
# Invoke via the shared read-only Picinae environment wrapper, repo root.
set -euo pipefail
export PROOF_MEMORY_KB=2000000
ulimit -v 2000000
ulimit -s 65536
query=$(mktemp -d "$PWD/_build/e08-assumptions.XXXXXXXX")
trap 'rm -rf -- "$query"' EXIT
python3 - "$query/Assumptions.v" <<'PY'
import json,sys
from pathlib import Path
coverage=json.loads(Path('Examples/claude/lifter/scalar_ports/COVERAGE.json').read_text())
with open(sys.argv[1],'w') as f:
 for r in coverage['accepted']:
  module='Picinae.Examples.claude.lifter.scalar_ports.'+r['artifact']
  f.write(f'Require Import {module}.\nCheck {module}.welltyped.\nPrint Assumptions {module}.welltyped.\n')
PY
rocq compile -q -R _build/default Picinae "$query/Assumptions.v"
