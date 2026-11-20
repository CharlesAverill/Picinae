#!/usr/bin/env python3
"""Receipt validation remains mandatory even if the Ghidra launcher returns 0."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('supervisor',Path(__file__).with_name('lift-x64.py'))
supervisor=importlib.util.module_from_spec(spec);spec.loader.exec_module(supervisor)


class Tests(unittest.TestCase):
    def test_incomplete_stale_mismatched_and_partial_receipts(self):
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp)
            (stage/'e25_abs_amd64.v').write_text('partial')
            # A swallowed launcher exception with partial output cannot pass.
            with self.assertRaises(FileNotFoundError):supervisor.validate_receipt(stage,'fresh',['abs'],'elf','glibc','strict')
            (stage/'e25_abs_amd64.pcode.json').write_text('[]')
            sha=lambda p:hashlib.sha256((stage/p).read_bytes()).hexdigest()
            good=dict(token='fresh',elf_sha256='elf',source_kind='glibc',profile='strict',language='x86:LE:64:default',addressing='global',records=[dict(symbol='abs',output='e25_abs_amd64.v',output_sha256=sha('e25_abs_amd64.v'),pcode_sha256=sha('e25_abs_amd64.pcode.json'),instructions=1)])
            def validate(r):
                (stage/'SUCCESS.json').write_text(json.dumps(r))
                return supervisor.validate_receipt(stage,'fresh',['abs'],'elf','glibc','strict')
            validate(good)
            for field,val in [('token','stale'),('records',[]),('elf_sha256','wrong'),('source_kind','synthetic'),('profile','cet-disabled'),('language','AARCH64:LE:64:v8A'),('addressing','relative')]:
                r=copy.deepcopy(good);r[field]=val
                with self.assertRaises(ValueError):validate(r)
            for field,val in [('output','elsewhere.v'),('output_sha256','bad'),('pcode_sha256','bad'),('instructions',0)]:
                r=copy.deepcopy(good);r['records'][0][field]=val
                with self.assertRaises((ValueError,FileNotFoundError)):validate(r)
            extra=stage/'unexpected.v';extra.write_text('partial')
            with self.assertRaises(ValueError):validate(good)
            extra.unlink()
            (stage/'e25_abs_amd64.pcode.json').unlink()
            with self.assertRaises(FileNotFoundError):validate(good)


if __name__=='__main__':unittest.main(verbosity=2)
