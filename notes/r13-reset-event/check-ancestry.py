import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
prereq='5fec2fc24d0c739bafc08add426f02a3085e15cd'
def git(*args): return subprocess.check_output(['git',*args],text=True).strip()
assert git('branch','--show-current')=='llm-proofs/r13-reset-event'
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base',base,'HEAD')==base
assert git('merge-base',prereq,'HEAD')==prereq
allowed=set(git('rev-list',base+'..'+prereq).splitlines())
actual=set(git('rev-list',base+'..HEAD').splitlines())
assert allowed<=actual
print('Base:',base,'\nAllowed prerequisite:',prereq)
print('Accepted prerequisite commits:',len(allowed))
for commit in actual-allowed:
    parents=git('show','-s','--format=%P',commit).split()
    assert len(parents)==1,(commit,parents)
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert all(p=='dune' or p=='Examples/FreeRTOS/armv6m_uxTaskResetEventItemValue_proof.v' or p.startswith('notes/r13-reset-event/') for p in paths),(commit,paths)
    print('Scoped own commit:',commit)
print(git('log','--format=%H %s',base+'..HEAD'))
print('ANCESTRY PASS')
