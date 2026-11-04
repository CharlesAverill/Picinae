#!/usr/bin/env python3
"""Preserve old tests; redirect their one hardcoded temporary directory privately.
Option --integrated reruns each family's complete suite through the dispatcher.
"""
import sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
state=Path('/home/charles/code/friends/.toolchains/e39-x86-backend-integration')
(state/'tmp').mkdir(parents=True,exist_ok=True)
tempfile.tempdir=str(state/'tmp')
original=tempfile.TemporaryDirectory
def private_temp(*args,**kwargs):
    if 'dir' in kwargs and str(kwargs['dir']).startswith('/home/charles/code/friends/.toolchains/'):
        kwargs['dir']=state/'tmp'
    return original(*args,**kwargs)
modules=['test_scalar','test_x64','test_x64_copy','test_x64_rep','test_bitscan','test_x64_publication','test_bitscan_publication','test_x64_rep_publication','test_x64_integrated']
with patch.object(tempfile,'TemporaryDirectory',private_temp):
    if '--integrated' in sys.argv:
        import test_x64,test_x64_copy,test_x64_rep,test_bitscan
        from pcode2coq_x64_integrated import IntegratedLifter
        test_x64.X64Lifter=IntegratedLifter
        test_x64_copy.CopyLifter=IntegratedLifter
        test_x64_rep.X64RepLifter=IntegratedLifter
        test_bitscan.X64Lifter=IntegratedLifter
    suite=unittest.TestLoader().loadTestsFromNames(modules)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    sys.exit(not result.wasSuccessful())
