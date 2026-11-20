from pathlib import Path
import re

def declarations(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    text = re.sub(r'Proof\..*?Qed\.', '', text, flags=re.S)
    text = text.replace('Abort.', '')
    return ' '.join(text.split())

initial = Path('notes/r42-port-mask/initial-attempt.v.txt').read_text()
final = Path('Examples/FreeRTOSMask/armv6m_port_mask_proof.v').read_text()
assert declarations(initial) == declarations(final)
print('PASS: every original definition and theorem statement is retained.')
print('Unchecked proof bodies are Abort; exact initial attempt remains in initial-attempt.v.txt.')
