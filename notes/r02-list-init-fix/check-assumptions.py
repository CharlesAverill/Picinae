from pathlib import Path
import re

source = Path('Examples/FreeRTOS/armv6m_vListInitialise_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Lemma) (\w+):', source, re.M)
raw = Path('notes/r02-list-init-fix/12-assumptions.log').read_text()
assert len(names) == 12
assert raw.rstrip().endswith('EXIT_CODE=0')
expected_fe = {'list_init_correct', 'list_init_at_bx', 'list_init_return_step'}
fe = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
for i, name in enumerate(names):
    begin = re.search(r'^' + name + r'\n', raw, re.M)
    assert begin, name
    end = re.search(r'^' + names[i+1] + r'\n', raw, re.M).start() if i+1 < len(names) else raw.index('\nEXIT_CODE=0')
    section = raw[begin.end():end].strip()
    if name in expected_fe:
        assumptions = section[section.index('Axioms:'):]
        assert assumptions == fe, (name, assumptions)
        assert 'Closed under the global context' not in section
        print(name + ': inherited functional_extensionality_dep only')
    else:
        assert section.endswith('Closed under the global context'), name
        assert 'Axioms:' not in section
        print(name + ': Closed under the global context')
print('PASS: 12 transitive queries; nine closed, three inherited-FE-only; no imported admission')
print('\nVerbatim common assumptions block for the three named results:\n' + fe)
