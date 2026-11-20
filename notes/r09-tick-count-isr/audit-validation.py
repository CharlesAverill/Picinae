"""Check one-shot retention and every raw transitive assumptions report."""
from pathlib import Path
import re
root = Path('notes/r09-tick-count-isr')
proof = Path('Examples/FreeRTOS/armv6m_xTaskGetTickCountFromISR_proof.v').read_bytes()
assert proof == (root/'initial-attempt.v.txt').read_bytes()
names = re.findall(r'^(?:Theorem|Lemma|Corollary) (\w+)', proof.decode(), re.M)
assert len(names) == 12
log = (root/'assumptions.log').read_text()
assert log.endswith('EXIT_CODE=0\n')
assert (root/'initial-build.log').read_text().endswith('EXIT_CODE=0\n')
fe = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
for i, name in enumerate(names):
    match = re.search(r'^'+name+r'\s*\n', log, re.M)
    assert match, name
    chunk = log[match.end():]
    if i + 1 < len(names):
        end = re.search(r'^'+names[i+1]+r'\s*\n', chunk, re.M)
        assert end
        chunk = chunk[:end.start()]
    expected = 'Closed under the global context' if i < 6 else fe
    assert expected in chunk, (name, chunk)
    if i < 6:
        assert 'Axioms:' not in chunk
    else:
        assert 'Axioms:' not in chunk.replace(fe, '')
    print(name+': '+('closed' if i < 6 else 'inherited FunctionalExtensionality.functional_extensionality_dep only'))
assert log.count('Closed under the global context') == 6
assert log.count('Axioms:') == 6
print('PASS: 12 initial statements/proofs unchanged; 6 closed, 6 inherited-FE-only.')
