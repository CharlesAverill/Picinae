from pathlib import Path
import re
initial=Path('notes/r26-next-unblock/initial-attempt.v.txt').read_text()
current=Path('Examples/FreeRTOS/armv6m_prvResetNextTaskUnblockTime_proof.v').read_text()
pattern=r'^(?:Theorem|Lemma|Corollary)\s+\w+\b.*?(?=\n(?:Proof\.|\(\* PARTIAL:))'
a=re.findall(pattern,initial,re.M|re.S)
b=re.findall(pattern,current,re.M|re.S)
assert len(a)==16 and a==b, (len(a),len(b))
assert current.count('Abort.')==6
assert current.count('Qed.')==10
assert initial[:initial.index('Theorem next_unblock_correct :')].split('Require Import',1)[1]==current[:current.index('Theorem next_unblock_correct :')].split('Require Import',1)[1]
print('PASS: all 16 declaration statements unchanged; first 10 helper proofs unchanged; six execution/return attempts now Abort; entire initial attempt preserved.')
