#!/usr/bin/env python3
"""Inspect every raw transitive report; permit only the documented baseline FE."""
from pathlib import Path
import re

source = Path('Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Lemma|Corollary) (\w+)', source, re.M)
raw = Path('notes/r11-missed-yield-fix/assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
parts = re.split(r'(?m)^(missed_yield_\w+)\n', raw)[1:]
assert parts[::2] == names and len(names) == 18, parts[::2]
closed = inherited = 0
for name, output in zip(parts[::2], parts[1::2]):
    if 'Closed under the global context' in output:
        assert 'Axioms:' not in output
        closed += 1
        print(name + ': closed')
    else:
        assert output.count('Axioms:') == 1
        axioms = re.findall(r'(?m)^([^ \n].*?)\s*:', output.split('Axioms:')[1])
        assert axioms == ['FunctionalExtensionality.functional_extensionality_dep'], axioms
        inherited += 1
        print(name + ': inherited FunctionalExtensionality.functional_extensionality_dep only')
print(f'PASS: {closed} closed, {inherited} inherited-FE-only; all 18 reports inspected')
print('PASS: no imported admitted proof or additional axiom in any transitive report')
