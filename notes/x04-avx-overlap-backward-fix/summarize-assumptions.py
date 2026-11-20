from pathlib import Path
import re
source = Path('notes/x04-avx-overlap-backward/initial-attempt.v.txt').read_text()
names = re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', source, re.M)
raw = Path('notes/x04-avx-overlap-backward-fix/14-assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
closed = fe = 0
for i, name in enumerate(names):
    start = re.search(r'^' + re.escape(name) + r'\s*\n', raw, re.M)
    assert start, name
    end = re.search(r'^' + re.escape(names[i+1]) + r'\s*\n', raw[start.end():], re.M) if i+1 < len(names) else None
    block = raw[start.end():start.end()+end.start()] if end else raw[start.end():]
    if 'Axioms:' in block:
        assumptions = block.split('Axioms:', 1)[1].split('EXIT_CODE=', 1)[0].strip()
        expected = '''FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
        assert assumptions == expected, (name, assumptions)
        fe += 1
        print(name + ': inherited FE only')
        print('Axioms:\n' + assumptions)
    else:
        assert 'Closed under the global context' in block, name
        closed += 1
        print(name + ': Closed under the global context')
print(f'PASS: {len(names)} certificates; {closed} closed, {fe} inherited FE only; no imported admission')
