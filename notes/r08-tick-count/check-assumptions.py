"""Reject unexpected transitive assumptions in the complete raw audit."""
from pathlib import Path
import re

source = Path('Examples/FreeRTOS/armv6m_xTaskGetTickCount_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Lemma|Corollary) (\w+)', source, re.M)
raw = Path('notes/r08-tick-count/assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
assert 'RELEASED r08-tick-count exit=0' in raw
allowed = 'FunctionalExtensionality.functional_extensionality_dep'
closed = dependent = 0
for i, name in enumerate(names):
    start = re.search(r'^' + re.escape(name) + r'\s*$', raw, re.M)
    assert start, name
    stop = re.search(r'^' + re.escape(names[i+1]) + r'\s*$', raw, re.M) if i+1 < len(names) else None
    block = raw[start.end():stop.start() if stop else len(raw)]
    if 'Closed under the global context' in block:
        assert 'Axioms:' not in block
        closed += 1
        print(name + ': Closed under the global context')
    else:
        assert 'Axioms:' in block, name
        axioms = block.split('Axioms:', 1)[1].split('RELEASED', 1)[0].strip()
        assert axioms.startswith(allowed + ' :\n'), (name, axioms)
        # Each assumption name is unindented; its type is indented.
        declared = [line for line in axioms.splitlines() if line and not line[0].isspace()]
        assert declared == [allowed + ' :'], (name, declared)
        dependent += 1
        print(name + ': ' + allowed)
assert closed + dependent == len(names) == 12
print(f'PASS: all {len(names)} exported facts queried; {closed} closed; {dependent} inherited-FE-only; no admitted proof dependency')
