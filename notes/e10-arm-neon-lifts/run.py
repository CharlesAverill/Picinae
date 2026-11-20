#!/usr/bin/env python3
"""Record exact argv, cwd, and actual exit; retain failed logs."""
import json,os,subprocess,sys
from pathlib import Path
name,*cmd=sys.argv[1:]
log=Path(__file__).resolve().parent/'logs'/name
with log.open('w') as f:
 f.write('COMMAND='+json.dumps(cmd)+'\nCWD='+os.getcwd()+'\n'); f.flush()
 r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
 f.write('\nEXIT_CODE='+str(r.returncode)+'\n')
print(str(log)+': EXIT_CODE='+str(r.returncode))
sys.exit(r.returncode)
