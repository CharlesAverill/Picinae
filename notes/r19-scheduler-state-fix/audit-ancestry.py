import subprocess
BASE='49956416928e5b6bb3928b54ae33e3b81091f006'
PREREQ='47a4a26a7e155fdfa1d045fddb288f68bf343a6b'
def git(*args): return subprocess.check_output(['git',*args],text=True).strip()
assert git('rev-parse','origin/llm_generated_proofs')==BASE
assert git('merge-base','origin/llm_generated_proofs','HEAD')==BASE
assert git('merge-base',PREREQ,'HEAD')==PREREQ
assert git('branch','--show-current')=='llm-proofs/r19-scheduler-state-fix'
allowed=set(git('rev-list',BASE+'..'+PREREQ).splitlines())
actual=set(git('rev-list',BASE+'..HEAD').splitlines())
own=set(git('rev-list',PREREQ+'..HEAD').splitlines())
assert actual==allowed|own
for commit in own:
 for path in git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines():
  assert path=='dune' or path=='Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v' or path.startswith('notes/r19-scheduler-state-fix/'),(commit,path)
assert not git('diff',PREREQ,'--','Examples/FreeRTOS/xTaskGetSchedulerState_armv6m.v', 'notes/r19-scheduler-state')
assert git('rev-parse','llm-proofs/r19-scheduler-state')==PREREQ
print('HEAD',git('rev-parse','HEAD'))
print('merge-base',git('merge-base','origin/llm_generated_proofs','HEAD'))
print('Allowed prerequisites:',len(allowed),'Own scoped commits:',len(own))
print('git log --format=%H %s origin/llm_generated_proofs..HEAD')
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print('git diff --stat origin/llm_generated_proofs...HEAD')
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('git diff --stat '+PREREQ)
print(git('diff','--stat',PREREQ))
print('git status --porcelain=v1')
print(git('status','--porcelain=v1'))
print('PASS: exact assigned ancestry; generated lift unchanged; only scoped own commits')
