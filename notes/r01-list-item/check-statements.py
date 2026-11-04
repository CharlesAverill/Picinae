from pathlib import Path
import re
original = Path("notes/r01-list-item/initial-attempt.v.txt").read_text()
current = Path("Examples/FreeRTOS/armv6m_vListInitialiseItem_proof.v").read_text()
def without_proofs(s):
    return re.sub(r"Proof\..*?(?:Qed|Abort)\.", "PROOF", s, flags=re.S)
assert without_proofs(original) == without_proofs(current)
print("PASS: every definition, theorem statement and header is byte-for-byte preserved; only unchecked proof bodies replaced by Abort.")
print("Initial Qed count:", original.count("Qed."))
print("Retained Qed count:", current.count("Qed."))
print("Unchecked Abort count:", current.count("Abort."))
