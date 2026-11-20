#!/usr/bin/env python3
"""Check original author declarations and evidence preservation."""
import re, subprocess, pathlib, hashlib
old = pathlib.Path('notes/a-memset-emag/initial-attempt.v.txt').read_text()
new = pathlib.Path('Examples/claude/arm8_memset_emag_proof.v').read_text()
pattern = r'(?ms)^(?:Theorem|Lemma)\s+(\w+)\s*:(.*?)\nProof\.'
initial = dict(re.findall(pattern, old))
current = dict(re.findall(pattern, new))
assert len(initial) == 22, len(initial)
for name, statement in initial.items():
    assert current[name] == statement, name
print('All 22 original theorem/lemma statements preserved verbatim.')
subprocess.run(['git', 'diff', '--exit-code', '4b2f5bc78d3f544645dae5fb9f3714faf2db68dc', '--',
 'notes/a-memset-emag', 'Examples/claude/lifter/scalar_ports/e08___memset_emag_arm8.v'], check=True)
for p in ['Examples/claude/lifter/scalar_ports/e08___memset_emag_arm8.v',
          'notes/a-memset-emag/initial-attempt.v.txt']:
    print(hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(), p)
