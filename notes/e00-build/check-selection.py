#!/usr/bin/env python3
"""Check the objects produced by e00's clean selective build."""
from pathlib import Path

root = Path('_build/default')
core = sorted(p.name for p in root.glob('*.vo'))
examples = sorted(p.relative_to(root).as_posix() for p in root.rglob('*.vo')
                  if p.parent != root)
print('Core:', *core, sep='\n')
print('Examples:', *examples, sep='\n')
assert len(core) == 14, core
assert examples == ['Examples/claude/' + p + '.vo' for p in (
    'abs_amd64', 'abs_arm8', 'amd64_abs_proof', 'amd64_common',
    'arm8_abs_proof', 'arm8_common')], examples
print('PASS: exactly fourteen core and six selected example objects; '
      'no excluded proof objects')
