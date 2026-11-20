from pathlib import Path
import re, subprocess, hashlib
source = Path('Examples/FreeRTOS/armv6m_prvResetNextTaskUnblockTime_proof.v').read_text()
archive = Path('notes/r26-next-unblock/initial-attempt.v.txt').read_bytes()
original = subprocess.check_output(['git', 'show', '9cdc8b9ede899efa594dc84a55f33e85616c9091:notes/r26-next-unblock/initial-attempt.v.txt'])
assert archive == original
pattern = r'^(?:Theorem|Lemma|Corollary)\s+\w+\b.*?(?=\n(?:Proof\.|\(\* WIP:))'
statements = re.findall(pattern, archive.decode(), re.M | re.S)
current = re.findall(pattern, source, re.M | re.S)
assert len(statements) == 16
assert all(s in current for s in statements)
# Every original definition, including ABI, exit, invariant and witness, stays exact.
pattern = r'^Definition\s+\w+\b.*?\.\n'
assert re.findall(pattern, archive.decode(), re.M | re.S) == re.findall(pattern, source, re.M | re.S)
print('PASS: all 16 original declarations and all definitions unchanged')
print('Archive SHA256:', hashlib.sha256(archive).hexdigest())
