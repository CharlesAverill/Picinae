#!/usr/bin/env bash
set -eu
probe_dir=$(mktemp -d /tmp/a-strcmp-complete.XXXXXXXX)
trap 'rm -rf "$probe_dir"' EXIT
python3 - "$probe_dir/Probe.v" <<'PY'
import hashlib
from pathlib import Path
import re
import sys
source=Path('notes/a-strcmp-complete/mask-helpers.v.txt').read_bytes()
sha=hashlib.sha256(source).hexdigest()
Path('notes/a-strcmp-complete/probe-source-'+sha+'.v.txt').write_bytes(source)
print('PROBE_SOURCE_SHA256='+sha, flush=True)
header='''Require Import Picinae_armv8.
Require Import Picinae.Examples.claude.arm8_strcmp_proof.
Require Import arm8_common.
From Stdlib Require Import NArith ZArith Lia List.
Import ARM8Notations ListNotations.
Open Scope N.
'''
s=source.decode()
s=re.sub(r'((?:Lemma|Theorem)\s+(\w+)\b.*?Qed\.)',lambda m:m[1]+'\nPrint Assumptions '+m[2]+'.',s,flags=re.S)
Path(sys.argv[1]).write_text(header+s)
PY
rocq compile -q -R _build/default Picinae "$probe_dir/Probe.v"
