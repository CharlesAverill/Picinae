"""Run unchanged historical launchers with private e39 mutable paths only.
Replay receipts stay historical-format evidence, never current combined receipts.
"""
import importlib.util
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
STATE=Path('/home/charles/code/friends/.toolchains/e39-x86-backend-integration')
UNITS={'e25':('e25-x86-scalar-driver','lift-x64.py'),'e26':('e26-x86-sse-avx-lowering','lift-x64-copy.py'),'e27':('e27-x86-rep-lowering','lift-x64-rep.py'),'e28':('e28-x86-bitscan-lowering','lift-bitscan.py')}
def main(unit):
    filename=UNITS[unit][1]
    spec=importlib.util.spec_from_file_location('historical',ROOT/'tools/ghidra-lifter'/filename)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    module.DEFAULT_STATE=str(STATE/'compat'/unit)
    return module.main()
if __name__=='__main__':
    unit=sys.argv.pop(1)
    raise SystemExit(main(unit))
