#!/usr/bin/env python3
import re
from pathlib import Path
s=Path('Examples/claude/amd64_memmove_avx_overlap_forward_proof.v').read_text()
raw=Path('notes/x03-avx-overlap-forward-fix/12-assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
names=re.findall(r'^(?:Theorem|Lemma|Corollary) (\w+)\b',s,re.M)
assert len(names)==18
fe={'ofw_welltyped','memmove_avx_correct_overlap_forward','memmove_avx_overlap_forward_at_ret'}
for i,name in enumerate(names):
    start=re.search(r'^'+name+r'\n',raw,re.M).end()
    ends=[m.start() for m in re.finditer(r'^('+ '|'.join(names)+r')\n',raw,re.M) if m.start()>=start]
    segment=raw[start:min(ends) if ends else len(raw)]
    if name in fe:
        expected='Axioms:\nFunctionalExtensionality.functional_extensionality_dep :\n  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),\n  (forall x : A, f x = g x) -> f = g'
        assert expected in segment, name
        assert segment.count('Axioms:')==1 and segment.count(' :\n')==1, name
        assert 'Closed under the global context' not in segment
        print(name+': inherited Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep only')
    else:
        assert 'Closed under the global context' in segment and 'Axioms:' not in segment, name
        print(name+': Closed under the global context')
print('All 18 results inspected: 15 closed, 3 inherited-FE-only; no imported admission.')
