#!/usr/bin/env python3
import subprocess
from pathlib import Path
baseline='4c17e59'
def git(*args):
    return subprocess.check_output(['git',*args])
paths=git('ls-tree','-r','--name-only',baseline).decode().splitlines()
for p in paths:
    if p=='dune': continue
    assert Path(p).read_bytes()==git('show',baseline+':'+p),p
old=git('show',baseline+':dune').decode()
expected=old.replace('  Examples.FreeRTOS.armv6m_list_model\n',
    '  Examples.FreeRTOS.armv6m_list_model\n  Examples.FreeRTOS.armv6m_list_refinement\n')
assert Path('dune').read_text()==expected
print('PASS: all',len(paths)-1,'inherited files byte-identical to authorized integration')
print('PASS: dune only adds Examples.FreeRTOS.armv6m_list_refinement')
