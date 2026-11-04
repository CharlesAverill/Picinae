#!/usr/bin/env bash
set -euo pipefail
ulimit -v 6000000
ulimit -s 65536
scratch=$(mktemp -d "$PWD/_build/witnesses.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
python3 - "$scratch/Witnesses.v" <<'PY'
import sys
from pathlib import Path
s=Path('Examples/claude/amd64_memmove_avx_overlap_forward_proof.v').read_text()
header=s[s.index('Require Import Picinae_amd64'):s.index('Definition ofw_postcondition')]
body=s[s.index('Definition ofw_witness_memory'):]
Path(sys.argv[1]).write_text(header+body)
PY
rocq compile -q -R _build/default Picinae "$scratch/Witnesses.v"
