"""Summarize, without replacing, the verbatim transitive assumptions log."""
from pathlib import Path
import re
text = Path('notes/a-wcschrnul-fix/assumptions.log').read_text()
assert text.endswith('EXIT_CODE=0\n')
blocks = re.findall(r'(?ms)^(wcschrnul_\w+)\n(.*?)(?=^wcschrnul_|^RELEASED)', text)
assert len(blocks) == 11
closed, fe = [], []
for name, block in blocks:
    if 'Closed under the global context' in block:
        assert 'Axioms:' not in block
        closed.append(name)
        print(f'{name}: Closed under the global context')
    else:
        assumptions = block.split('Axioms:\n', 1)[1]
        assert assumptions == ('FunctionalExtensionality.functional_extensionality_dep :\n'
            '  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),\n'
            '  (forall x : A, f x = g x) -> f = g\n')
        fe.append(name)
        print(f'{name}: inherited functional_extensionality_dep only')
assert fe == ['wcschrnul_welltyped', 'wcschrnul_correct', 'wcschrnul_return']
print(f'{len(closed)} closed; {len(fe)} inherited-FE-only; no other transitive assumptions.')
