#!/usr/bin/env python3
import importlib.util,re
from pathlib import Path
spec=importlib.util.spec_from_file_location('audit','tools/audit-proof-source.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
def declarations(path):
    source=audit.mask(Path(path).read_text())
    source=re.sub(r'\bProof\.(?:.|\n)*?\b(?:Qed|Defined|Abort)\.', '', source)
    source=re.sub(r'Print Assumptions [^.]+\.', '', source)
    return ' '.join(source.split())
a='notes/r05-list-insert/initial-attempt.v.txt'
b='Examples/FreeRTOS/armv6m_vListInsert_proof.v'
assert declarations(a)==declarations(b), 'Statement/definition changed'
print('PASS: all initial statements and definitions preserved exactly (whitespace/comments ignored)')
