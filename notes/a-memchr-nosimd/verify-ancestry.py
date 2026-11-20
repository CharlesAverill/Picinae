import subprocess

def git(*args):
    return subprocess.check_output(['git',*args],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
pre='bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9'
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
subprocess.run(['git','merge-base','--is-ancestor',pre,'HEAD'],check=True)
allowed=set(git('rev-list',base+'..'+pre).splitlines())
actual=set(git('rev-list',base+'..HEAD').splitlines())
own=set(git('rev-list',pre+'..HEAD').splitlines())
assert actual==allowed|own
for commit in own:
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert all(p=='dune' or p.startswith('notes/a-memchr-nosimd/') or p in (
        'Examples/claude/arm8_memchr_nosimd_spec.v',
        'Examples/claude/arm8_memchr_nosimd_proof.v') for p in paths), (commit,paths)
print('MERGE_BASE',base)
print('ACCEPTED_PREREQUISITE',pre)
print('ALLOWED_PREREQUISITE_COMMITS',len(allowed))
print('OWN_SCOPED_COMMITS',len(own))
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print('DIFF_STAT_FROM_ORIGIN')
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('DIFF_STAT_FROM_PREREQUISITE')
print(git('diff','--stat',pre+'...HEAD'))
print('STATUS')
print(git('status','--short'))
