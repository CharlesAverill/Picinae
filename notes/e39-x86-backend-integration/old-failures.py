"""Execute all four historical real-negative suites, redirecting state/launchers.
The fixture/symbol expectations and assertions are unchanged.
"""
from pathlib import Path
from compat import ROOT,STATE,UNITS
for unit,(directory,driver) in UNITS.items():
    (STATE/'compat'/unit/'replays').mkdir(parents=True,exist_ok=True)
    (STATE/'compat'/unit/'projects').mkdir(exist_ok=True)
    source=ROOT/'notes'/directory/'check-failures.py'
    text=source.read_text().replace('/home/charles/code/friends/.toolchains/'+directory,str(STATE/'compat'/unit))
    text=text.replace('tools/ghidra-lifter/'+driver,'notes/e39-x86-backend-integration/compat-'+unit+'.py')
    print('HISTORICAL SUITE',unit,'private state',STATE/'compat'/unit,flush=True)
    exec(compile(text,str(source),'exec'),{'__name__':'__main__','__file__':str(source)})
