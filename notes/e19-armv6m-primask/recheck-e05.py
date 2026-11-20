#!/usr/bin/env python3
"""Run unchanged e05 generator, comparing all artifacts without any writes.

The only permitted metadata delta is coverage.json's frontend source hash.
Use an in-memory replacement of the final comparison expression to expose this
expected delta. __file__ remains the real, unchanged e05 source for its digest.
"""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
path = root/'Examples/freertos/cortex-m0/extract.py'
count = 0

def compare_artifact(path, expected):
    global count
    actual = path.read_text()
    if path == root/'Examples/FreeRTOS/coverage.json':
        old, new = json.loads(actual), json.loads(expected)
        prior, current = old.pop('frontend_sha256'), new.pop('frontend_sha256')
        assert old == new, 'unexpected e05 coverage change'
        assert current == hashlib.sha256((root/'lifter/armv6m.py').read_bytes()).hexdigest()
        print(f'EXPECTED provenance-only frontend_sha256 delta: {prior} -> {current}')
    else:
        assert actual == expected, f'non-reproducible e05 artifact: {path}'
    count += 1

original = "assert path.read_text() == expected, f'non-reproducible artifact: {path}'"
source = path.read_text()
assert source.count(original) == 1
source = source.replace(original, 'compare_artifact(path, expected)')
source = source.replace("print(f'PASS: {len(paths)} artifacts reproduced byte-for-byte')", "print(f'PASS: {len(paths)-1} artifacts byte-identical; coverage only frontend hash differs')")
namespace = {'__file__':str(path),'__name__':'e19_recheck_e05','compare_artifact':compare_artifact}
exec(compile(source,str(path),'exec'),namespace)
sys.argv = [str(path), *sys.argv[1:]]
namespace['main']()
assert count == 90
