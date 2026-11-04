"""Check the recorded raw assumptions, declarations and final full objects."""
import hashlib
import re
from pathlib import Path

root = Path('notes/r10-suspend-all-fix')
source = Path('Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.v')
text = source.read_text()
names = re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)', text, re.M)
assert len(names) == 16
assert len(re.findall(r'\bQed\.', text)) == 16
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b', text)
raw = (root/'14-all-assumptions.log').read_text()
assert raw.endswith('EXIT_CODE=0\n')
assert 'ADMITTED r10-suspend-all-fix memory_kib=1750000' in raw
expected_fe = {
    'suspend_all_correct', 'suspend_all_post_at_bx',
    'suspend_all_original_memory_effects', 'suspend_all_preserves_callee_saved',
    'suspend_all_return_step', 'suspend_all_caller_result',
}
fe = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
for i, name in enumerate(names):
    start = raw.index('\n'+name+'\n')+1
    end = raw.index('\n'+names[i+1]+'\n', start) if i+1 < len(names) else raw.index('\nRELEASED', start)
    block = raw[start:end]
    if name in expected_fe:
        assert block.count('Axioms:') == 1
        assert block[block.index('Axioms:'):].strip() == fe, name
        print(name + ': inherited functional_extensionality_dep only')
    else:
        assert block.rstrip().endswith('Closed under the global context'), name
        assert 'Axioms:' not in block, name
        print(name + ': Closed under the global context')
assert raw.count('Axioms:') == 6
assert raw.count('Closed under the global context') == 10
print('PASS: all 16 raw transitive queries inspected; 10 closed, six inherited FE only; no imported admission')
for path in [source, Path('_build/default')/source,
             Path('_build/default/Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.vo')]:
    assert path.is_file() and path.stat().st_size > 0
    print(hashlib.sha256(path.read_bytes()).hexdigest(), path.stat().st_size, path)
assert source.read_bytes() == (Path('_build/default')/source).read_bytes()
assert '(mode vo)' in Path('dune').read_text()
for extension in ['vos', 'vok']:
    marker = Path('_build/default/Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.'+extension)
    assert not marker.exists() or marker.stat().st_size == 0
print('PASS: final source matches built source; full .vo target with mode vo; .vos/.vok are empty compiler markers')
