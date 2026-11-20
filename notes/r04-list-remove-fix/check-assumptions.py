from pathlib import Path
import re
source = Path('Examples/FreeRTOS/armv6m_uxListRemove_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Lemma) (\w+)', source, re.M)
log = Path('notes/r04-list-remove-fix/21-assumptions.log').read_text()
assert 'EXIT_CODE=0' in log
fe = {'list_remove_correct', 'list_remove_at_bx', 'list_remove_return_step', 'list_remove_returns'}
block = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
for i, name in enumerate(names):
    start = log.index('\n' + name + '\n')
    stop = log.index('\n' + names[i+1] + '\n') if i+1 < len(names) else log.index('\nEXIT_CODE=')
    section = log[start:stop]
    if name in fe:
        assert section.count('Axioms:') == 1 and section.rstrip().endswith(block), name
        print(name + ': inherited FE only')
    else:
        assert 'Axioms:' not in section and section.rstrip().endswith('Closed under the global context'), name
        print(name + ': Closed under the global context')
assert len(names) == 16 and log.count('Closed under the global context') == 12
assert log.count(block) == 4
print('PASS: 16 transitive queries: 12 closed, 4 inherited functional extensionality only')
