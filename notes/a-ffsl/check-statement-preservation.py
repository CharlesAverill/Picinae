"""Compare the archived author attempt with the aborted handoff, without Rocq."""
from pathlib import Path
import re

def statements(text):
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    text = re.sub(r"Proof\..*?(?:Qed|Abort)\.", "PROOF", text, flags=re.S)
    return "".join(text.split())

initial = Path("notes/a-ffsl/initial-attempt.v.txt").read_text()
handoff = Path("Examples/claude/arm8_ffsl_proof.v").read_text()
assert statements(initial) == statements(handoff)
assert len(re.findall(r"^Abort\.$", handoff, flags=re.M)) == 11
print("All theorem statements and definitions match the initial attempt.")
print("11 failed/unreached proof bodies are archived and aborted; no repair build.")
