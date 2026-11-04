import pathlib, re
notes = pathlib.Path(__file__).parent
sources = [pathlib.Path('Examples/claude') / (stem + '.v') for stem in
           ['arm8_memcpy_common', 'arm8_memcpy_small_proof']]
names = [m[1] for p in sources for m in
         re.finditer(r'(?m)^(?:Lemma|Theorem)\s+(\w+):', p.read_text())]
assert len(names) == 50, names
assert sum(len(re.findall(r'\bQed\.', p.read_text())) for p in sources) == 50
assert not any(re.search(r'(?m)^\s*(?:Abort|Admitted)\.', p.read_text()) for p in sources)
raw = (notes / '34-assumptions.log').read_text()
assert raw.endswith('EXIT_CODE=0\n')
allowed = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
closed = fe = 0
for name in names:
    head = re.search(r'(?m)^' + re.escape(name) + r'\n\s*:', raw)
    assert head, ('Missing Check / Print Assumptions output', name)
    tail = raw[head.end():]
    end = re.search(r'(?m)^\w+\n\s*:|^EXIT_CODE=', tail)
    if end:
        tail = tail[:end.start()]
    if 'Closed under the global context' in tail:
        assert 'Axioms:' not in tail, name
        closed += 1
        kind = 'CLOSED'
    else:
        assert allowed in tail, (name, tail)
        assumptions = tail[tail.index('Axioms:'):].strip()
        assert assumptions == allowed, (name, assumptions)
        fe += 1
        kind = 'INHERITED FE ONLY'
    print(name + ': ' + kind)
assert (closed, fe) == (14, 36), (closed, fe)
print('PASS: all 50 facts queried; 14 closed, 36 inherited FE only; no imported admission.')
