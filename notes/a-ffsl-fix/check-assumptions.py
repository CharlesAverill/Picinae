"""Check the actual kernel query output against the reviewed baseline only."""
from pathlib import Path
import re
raw = Path('notes/a-ffsl-fix/assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
axioms = re.findall(r'^([A-Za-z_][A-Za-z_0-9.]*) :$', raw, re.M)
assert axioms == ['FunctionalExtensionality.functional_extensionality_dep'] * 3, axioms
assert raw.count('Axioms:\n') == 3
assert raw.count('Closed under the global context') == 16
assert raw.index('ffsl_correct\n') < raw.index('Axioms:\n') < raw.index('ffsll_correct\n')
print('19 kernel assumption queries passed: 3 use only inherited functional_extensionality_dep; 16 are closed.')
print('The two public correctness theorems and typing use the reviewed Stdlib baseline; frames and arithmetic helpers are closed.')
