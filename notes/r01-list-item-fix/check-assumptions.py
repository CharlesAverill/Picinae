#!/usr/bin/env python3
"""Check that the raw query has exactly the reviewed transitive dependencies."""
from pathlib import Path
import re
source = Path('Examples/FreeRTOS/armv6m_vListInitialiseItem_proof.v').read_text()
names = re.findall(r'^(?:Theorem|Corollary) (\w+)', source, re.M)
raw = Path('notes/r01-list-item-fix/24-final-assumptions.log').read_text()
assert raw.endswith('EXIT_CODE=0\n')
fe = {'item_exact', 'item_correct', 'item_execution_witness',
      'item_return_step', 'item_execution_returns'}
axiom = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
blocks = re.split(r'(?m)^(item_\w+)\n', raw)
assert blocks[1::2] == names
for name, block in zip(blocks[1::2], blocks[2::2]):
    if name in fe:
        assert block.count('Axioms:') == 1 and axiom in block
        assert block.split('Axioms:')[1].split('\n\nEXIT_CODE=')[0].strip() == axiom.split('Axioms:')[1].strip()
        assert 'Closed under the global context' not in block
        print(name + ': inherited functional_extensionality_dep only')
    else:
        assert block.count('Closed under the global context') == 1
        assert 'Axioms:' not in block
        print(name + ': closed')
assert len(names) == 14
print('PASS: all 14 transitive queries; nine closed, five inherited FE-only; no imported admission')
