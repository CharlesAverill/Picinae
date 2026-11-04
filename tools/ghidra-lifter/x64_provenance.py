"""Reproducible local source closure, including imports inside function bodies.

Release archives and compiled SLEIGH contents are separately hash-verified by
the supervisor. This manifest binds their pin sources, not mutable file paths.
"""
import ast
import hashlib
import re
from pathlib import Path


def feature_profile(profile):
    match = re.fullmatch(r'integrated-(strict|cet-disabled);bmi1=(present|absent|unspecified);abm=(present|absent|unspecified)', profile)
    if not match:
        raise ValueError('invalid integrated profile')
    cet, bmi1, abm = match.groups()
    return dict(cet_disabled=cet == 'cet-disabled',
                bmi1=None if bmi1 == 'unspecified' else bmi1,
                abm=None if abm == 'unspecified' else abm)


def dependency_manifest(repo, kind):
    repo = Path(repo)
    roots = [repo/'tools/ghidra-lifter', repo/'Examples/claude/inventory/e01-x86-inventory']
    pending = [roots[0]/n for n in ('lift-x64-integrated.py', 'x64_integrated_headless.py')]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        tree = ast.parse(path.read_text())
        for node in ast.walk(tree):
            names = [a.name for a in node.names] if isinstance(node, ast.Import) else [node.module] if isinstance(node, ast.ImportFrom) else []
            for name in names:
                if not name:
                    raise ValueError('relative imports require an explicit closure rule')
                for root in roots:
                    candidate = root/(name.replace('.', '/')+'.py')
                    if candidate.is_file():
                        pending.append(candidate)
            # Future dynamic import mechanisms must gain an explicit rule,
            # rather than silently losing a dependency from receipts.
            if isinstance(node, ast.Call) and (isinstance(node.func, ast.Name) and node.func.id == '__import__' or isinstance(node.func, ast.Attribute) and node.func.attr in ('import_module', 'exec_module', 'spec_from_file_location')):
                raise ValueError('unresolved dynamic import in dependency closure')
    pins = ['Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json',
            'Examples/claude/inventory/e02-arm-inventory/artifacts.lock.json',
            'notes/e25-x86-scalar-driver/isa-pins.json']
    if kind == 'synthetic':
        pins += ['notes/e39-x86-backend-integration/fixture/'+n for n in ('mixed.S', 'mixed.so', 'pins.json', 'build.sh')]
    elif kind != 'glibc':
        raise ValueError('unsupported source kind')
    seen.update(repo/p for p in pins)
    return {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}
