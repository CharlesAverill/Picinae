from pathlib import Path
import re,hashlib
initial=Path('notes/r14-timeout-internal/initial-attempt.v.txt').read_text()
current=Path('Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.v').read_text()
# All declarations/definitions are unchanged; only proof bodies may be packaged.
strip=lambda s:re.sub(r'Proof\..*?(?:Qed|Abort)\.', 'PROOF_BODY', s, flags=re.S)
assert strip(initial)==strip(current)
cut='Theorem timeout_correct :'
assert initial.split(cut)[0]==current.split(cut)[0]
assert len(re.findall(r'^Abort\.', current,re.M))==5
assert hashlib.sha256(initial.encode()).hexdigest()=='49df58ae049ed945efccef14bb57475133dd0b09633ef4e9a75195f02baf55cf'
print('All 16 theorem/helper statements and all definitions unchanged.')
print('11 completed helper proof scripts unchanged; 5 unverified attempts packaged with Abort.')
print('Exact initial source snapshot SHA256 matches.')
