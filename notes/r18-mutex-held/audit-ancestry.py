import hashlib,subprocess
from pathlib import Path
def git(*args): return subprocess.check_output(['git',*args],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
head='5fec2fc24d0c739bafc08add426f02a3085e15cd'
allowed={'71470bffba65392adf1873a3df9f0cf0ca4f1ac9','59f696d32a5623cdfbceb9a1e0f91e2cc7c054c1','dac36c0a03088a90bb6e6385f82cb355d27cc204','5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b','abe7eda601a63d47eb70e765f4ae2c4ca235cca4','8c01958e73ec7fe959c60b29444505afbb599d13','075f59aca328e60e6376e2af01fa49925ab10e9d','95da7ab7cee78f09a528aed86c1dfaf29520a9a8','7042ff1b6abdf79e2b07a348c7ef9ed014126ded',head}
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert git('merge-base',head,'HEAD')==head
assert git('rev-list','--parents','-n1','71470bffba65392adf1873a3df9f0cf0ca4f1ac9').split()==['71470bffba65392adf1873a3df9f0cf0ca4f1ac9',base]
assert set(git('rev-list',base+'..'+head).splitlines())==allowed
assert git('branch','--show-current')=='llm-proofs/r18-mutex-held'
def scoped(p):return p in ['dune','Examples/FreeRTOS/armv6m_pvTaskIncrementMutexHeldCount_proof.v'] or p.startswith('notes/r18-mutex-held/')
for c in git('rev-list',head+'..HEAD').splitlines():
 assert len(git('rev-list','--parents','-n1',c).split())==2
 assert all(scoped(p) for p in git('diff-tree','--no-commit-id','--name-only','-r',c).splitlines())
assert all(scoped(p) for p in git('diff','--name-only',head).splitlines())
assert hashlib.sha256(Path('Examples/FreeRTOS/pvTaskIncrementMutexHeldCount_armv6m.v').read_bytes()).hexdigest()=='447b2821c35d983c36509cdbbe0bdd6e53c35a9594bcdd3af872c45ebb6dbf53'
print('PASS: exact 10-commit prerequisite forest plus only scoped linear unit commits; generated lift unchanged.')
for args in [('rev-parse','HEAD'),('merge-base','origin/llm_generated_proofs','HEAD'),('log','--format=%H %s','origin/llm_generated_proofs..HEAD'),('diff','--stat','origin/llm_generated_proofs...HEAD'),('status','--short')]:
 print('git '+' '.join(args)); print(git(*args))
