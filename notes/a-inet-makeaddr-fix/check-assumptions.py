"""Inspect every raw transitive Print Assumptions block, without hiding FE."""
from pathlib import Path
import re

directory = Path(__file__).resolve().parent
raw = (directory / 'logs/22-assumptions.log').read_text()
source = Path('Examples/claude/arm8_inet_makeaddr_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Lemma|Definition)\s+(\w+)', source, re.M)
assert len(names) == 27
names.append('welltyped')
expected_fe = {'inet_makeaddr_welltyped', 'inet_makeaddr_correct', 'welltyped'}
fe = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
starts = sorted((re.search(r'^' + name + r'\n', raw, re.M).start(), name)
                for name in names)
for i, (offset, name) in enumerate(starts):
    end = starts[i+1][0] if i+1 < len(starts) else len(raw)
    block = raw[offset:end]
    if name in expected_fe:
        assert block.count(fe) == 1
        assert block.count('Axioms:') == 1
        assert 'Closed under the global context' not in block
        print(name + ': inherited FE only (verbatim block retained in raw log)')
    else:
        assert block.count('Closed under the global context') == 1
        assert 'Axioms:' not in block
        print(name + ': Closed under the global context')
assert raw.count(fe) == 3
assert raw.count('Axioms:') == 3
assert raw.count('Closed under the global context') == 25
assert raw.rstrip().endswith('EXIT_CODE=0')
print('PASS: 28 transitive queries; 25 closed, three inherited-FE-only; no other assumptions.')
print('Verbatim inherited assumption:\n' + fe)
