from pathlib import Path
import subprocess,json
P=Path(__file__).resolve().parent
G=lambda *a:subprocess.check_output(['git',*a],text=True).strip()
a=json.loads((P/'allowed-prerequisites.json').read_text());base=a['base'];allowed=set(a['union'])
assert G('merge-base','origin/llm_generated_proofs','HEAD')==base
for h in a['heads']:assert subprocess.run(['git','merge-base','--is-ancestor',h,'HEAD']).returncode==0
actual=set(G('rev-list',base+'..HEAD').splitlines());own=actual-allowed
for h in own:
    subject=G('show','-s','--format=%s',h)
    assert 'e39' in subject or subject.startswith(('Compose reviewed','Record integrated')), (h,subject)
# Existing artifact/evidence bytes must agree with the owning exact prerequisite.
protected={}
for h,prefixes in [(a['heads'][0],['notes/e25-x86-scalar-driver','notes/e28-x86-bitscan-lowering','Examples/claude/lifter/x64_scalar_','Examples/claude/lifter/x64_bitscan_']), (a['heads'][1],['notes/e26-x86-sse-avx-lowering','Examples/claude/lifter/x64_copy_']), (a['heads'][2],['notes/e27-x86-rep-lowering','Examples/claude/lifter/x64_rep_'])]:
    paths=G('ls-tree','-r','--name-only',h).splitlines()
    for path in paths:
        if any(path.startswith(p) for p in prefixes):
            original=subprocess.check_output(['git','show',h+':'+path])
            assert Path(path).read_bytes()==original,path
            protected[path]=h
# No instruction-family source changes in integration.
for filename in ('pcode2coq_x64.py','pcode2coq_scalar.py','pcode2coq_bitscan.py'):
    path='tools/ghidra-lifter/'+filename
    assert Path(path).read_bytes()==subprocess.check_output(['git','show',a['heads'][0]+':'+path]),path
for h,filename in [(a['heads'][1],'pcode2coq_x64_copy.py'),(a['heads'][2],'pcode2coq_x64_rep.py')]:
    path='tools/ghidra-lifter/'+filename
    assert Path(path).read_bytes()==subprocess.check_output(['git','show',h+':'+path]),path
print('merge-base',base,'prerequisite commits',len(allowed),'own commits',sorted(own),'protected files',len(protected))
print(G('log','--oneline','origin/llm_generated_proofs..HEAD'))
print(G('diff','--stat','origin/llm_generated_proofs...HEAD'))
