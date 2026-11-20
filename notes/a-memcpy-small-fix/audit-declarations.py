import pathlib, re
root = pathlib.Path('.')
names = []
for stem in ['arm8_memcpy_common', 'arm8_memcpy_small_proof']:
    old = (root / 'notes/a-memcpy-small' / ('initial-' + stem + '.v.txt')).read_text()
    new = (root / 'Examples/claude' / (stem + '.v')).read_text()
    # Every initial predicate/definition and lemma/theorem statement is preserved.
    pattern = r'(?m)^(?:Definition|Lemma|Theorem)\s+(\w+)\b'
    for match in re.finditer(pattern, old):
        name = match[1]
        tail = old[match.start():]
        if tail.startswith('Definition'):
            decl = tail.split('.\n', 1)[0] + '.'
        else:
            decl = tail.split('\nProof.', 1)[0]
            names.append(name)
        assert decl in new, name
        print('UNCHANGED:', name)
print('Original theorem/lemma statements:', len(names))
assert len(names) == 16
