#!/usr/bin/env python3
"""Retain exact archived non-proof source, apart from final-producer attribution."""
from pathlib import Path
import re
original = Path("notes/r01-list-item/initial-attempt.v.txt").read_text()
current = Path("Examples/FreeRTOS/armv6m_vListInitialiseItem_proof.v").read_text()
expected = original.replace(
    "Validation and final proof producer: see notes/r01-list-item/README.md.",
    "Final proof producer: OpenAI gpt-6.1-sol, xhigh, priority.\n"
    "   Repair validation: see notes/r01-list-item-fix/README.md.")
def without_proofs(source):
    return re.sub(r"Proof\..*?(?:Qed|Abort)\.", "PROOF", source, flags=re.S)
assert without_proofs(expected) == without_proofs(current), "Non-proof source changed"
names = re.findall(r"^(?:Theorem|Corollary) (\w+)", original, re.M)
assert names == re.findall(r"^(?:Theorem|Corollary) (\w+)", current, re.M)
assert len(names) == current.count("Qed.") == 14
assert not re.search(r"\b(?:Abort|Admitted|admit|Axioms?|Parameters?)\b", current)
print("PASS: all definitions/predicates and all 14 original theorem statements byte-for-byte retained")
print("Only non-proof change: update final-producer attribution and validation-note path")
print("All 14 end in Qed; no missing/aborted declarations, admissions, axioms or parameters")
print("\n".join(names))
