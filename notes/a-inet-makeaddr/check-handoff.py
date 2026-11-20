from pathlib import Path
import hashlib, re, subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
allowed=set('''71470bffba65392adf1873a3df9f0cf0ca4f1ac9
081d0233cd6667803b3907343b2fea6dc9eba714
052521a753adbda077843ec7b259801282a7b1e9
378fe1b57514b9af3f017a72b4ca665910156cc7
9ae8e6800fa044797efd98372857e6ac89b18e1b
9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b'''.split())
def git(*args): return subprocess.check_output(['git',*args],text=True).strip()
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert set(git('rev-list',base+'..9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b').split())==allowed
assert git('branch','--show-current')=='llm-proofs/a-inet-makeaddr'
p=Path('Examples/claude/arm8_inet_makeaddr_proof.v'); current=p.read_text()
initial=Path('notes/a-inet-makeaddr/initial-attempt.v.txt').read_text()
pattern=r'(?:Theorem|Lemma)\s+[A-Za-z0-9_]+:[\s\S]*?(?=\nProof\.)'
assert re.findall(pattern,current)==re.findall(pattern,initial)
assert len(re.findall(pattern,current))==18
assert current.count('Qed.')==9 and current.count('Abort.')==9
assert current.split('Theorem inet_makeaddr_nwc:',1)[1].split('Lemma inet_bfm24_correct:',1)[0]==initial.split('Theorem inet_makeaddr_nwc:',1)[1].split('Lemma inet_bfm24_correct:',1)[0]
lift=Path('Examples/claude/lifter/scalar_bitforms/e29_inet_makeaddr_arm8.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest()=='41c9789da4f26019b8c8b9269f421d8f1ac74b0a34925d1b2b5d4c74a8d75ae8'
assert not Path('_build/default/Examples/claude/arm8_inet_makeaddr_proof.vo').exists()
print('PASS: exact allowed prerequisite set and base, assigned branch, 18 unchanged statements, nine unchanged Qed bodies, nine Abort bodies, generated map unchanged, failed target has no .vo.')
