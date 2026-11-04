from pathlib import Path
import re

source = Path('Examples/FreeRTOS/armv6m_vListInsertEnd_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Corollary|Definition|Fixpoint) (\w+)', source, re.M)
raw = Path('notes/r03-list-insert-end-fix/24-final-all-assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
assert len(names) == 44
assert raw.count('Closed under the global context') == 39
assert raw.count('Axioms:') == 5
axioms = set(re.findall(r'^([A-Za-z_][\w.]*) :', raw, re.M))
assert axioms == {'FunctionalExtensionality.functional_extensionality_dep'}
current = None
results = {}
for line in raw.splitlines():
    if line in names:
        current = line
    elif line == 'Closed under the global context':
        assert current not in results
        results[current] = 'closed'
    elif line == 'Axioms:':
        assert current not in results
        results[current] = 'inherited FE only'
assert set(results) == set(names)
expected_fe = {'insert_end_exact', 'insert_end_at_bx', 'insert_end_return_step',
               'insert_end_trace_returns', 'insert_end_ordinary_return_nonvacuity'}
assert {n for n in names if results[n] != 'closed'} == expected_fe
for n in names:
    print(n + ': ' + results[n])
print('PASS: all 44 declarations queried; 39 closed, five inherited FE only')
