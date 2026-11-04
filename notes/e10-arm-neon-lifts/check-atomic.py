#!/usr/bin/env python3
from copy import deepcopy
import json,subprocess,sys
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
from test_neon_loads import cases, malformed
state=Path('/home/charles/code/friends/.toolchains/e10-arm-neon-lifts/atomic01')
state.mkdir(exist_ok=False)
row=cases()[0]
variants=list(malformed(row))[:8]
for i,bad in enumerate(variants):
 inp,out=state/f'{i}.json',state/f'{i}.il'
 inp.write_text(json.dumps(bad))
 cmd=[sys.executable,'-c','import sys,json; from pathlib import Path; sys.path.insert(0,sys.argv[1]); from test_neon_loads import lower; result=lower(json.loads(Path(sys.argv[2]).read_text())); Path(sys.argv[3]).write_text(result)',str(repo/'tools/ghidra-lifter'),str(inp),str(out)]
 print('COMMAND='+json.dumps(cmd),flush=True)
 r=subprocess.run(cmd)
 print('EXIT_CODE='+str(r.returncode),flush=True)
 assert r.returncode==1 and not out.exists()
print('PASS eight malformed subprocess failures, no IL output')
