#!/usr/bin/env python3
"""Fresh replay of new accepted maps and exact partial frontiers."""
import argparse
import json
from pathlib import Path
import re
import shutil
from validate import STATE, ART, NOTES, lift, publish

p = argparse.ArgumentParser()
p.add_argument('--run', required=True)
p.add_argument('--collect', action='store_true', help='collect this unit\'s outputs for the first time')
a = p.parse_args()
assert re.fullmatch('[A-Za-z0-9_-]+', a.run)
run = STATE / a.run
run.mkdir(parents=True, exist_ok=False)
frontiers = json.loads((NOTES / 'TARGETS.json').read_text())
for r in frontiers:
    name = r['symbol']
    ok = r['status'] == 'supported-closed-map'
    raw, result = lift(run, name, [name], expected=0 if ok else 1)
    if ok:
        out = run / (name + '-published')
        for f in publish(raw, out):
            if a.collect: shutil.copyfile(out / f, ART / f)
            else: assert (out / f).read_bytes() == (ART / f).read_bytes(), f
        print('PASS deterministic complete map', name)
    else:
        reason = re.sub(r'; no output accepted; Ghidra log:.*', '', result.stdout.strip())
        assert reason == r['reason'], (name, reason)
        print('PASS exact frontier and no-output failure', name)
