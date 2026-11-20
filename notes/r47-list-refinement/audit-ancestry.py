#!/usr/bin/env python3
import subprocess
from pathlib import Path
base='49956416928e5b6bb3928b54ae33e3b81091f006'
r03='7e49f57f76af3afaedf1c2b7bd5cf810cf4efef2'
r04='18dcb8cb928ba1e712aaa9aa8bb8f43aef51910f'
integration='4c17e59'
def git(*args):
    return subprocess.check_output(['git',*args],text=True).strip()
allowed=set(Path('notes/r47-list-refinement/allowed-prerequisites.txt').read_text().split())
assert allowed==set(git('rev-list',base+'..'+r03,base+'..'+r04).split())
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
integration=git('rev-parse',integration)
assert git('show','-s','--format=%P',integration).split()==[r03,r04]
actual=set(git('rev-list',base+'..HEAD').split())
extra=actual-allowed-{integration}
for c in extra:
    parents=git('show','-s','--format=%P',c).split()
    assert len(parents)==1,(c,parents)
    paths=git('diff-tree','--no-commit-id','--name-only','-r',c).splitlines()
    assert all(p in ['dune','Examples/FreeRTOS/armv6m_list_refinement.v'] or p.startswith('notes/r47-list-refinement/') for p in paths),(c,paths)
assert allowed<=actual
print('MERGE_BASE',base)
print('ALLOWED_PREREQUISITES',len(allowed))
print('IMPORT_MERGE',integration)
print('SCOPED_UNIT_COMMITS',*sorted(extra))
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('STATUS',git('status','--porcelain'))
print('ANCESTRY PASS')
