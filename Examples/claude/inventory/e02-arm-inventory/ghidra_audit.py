#@runtime PyGhidra
#@category Picinae
"""Decode the six historical lifts exactly; restricted toascii smoke adapter.

This is explicitly NOT a replacement for the unavailable modified pcode2coq.
Only the two-instruction toascii shape is accepted for the smoke lift.  We
call the pinned repository library's proc_insn, with per-instruction unique
renaming and strictFailure; no fallback or static-memory theorem generation.
"""
import argparse
import hashlib
import json
import pathlib
import re
import sys

repo, outdir = map(pathlib.Path, list(getScriptArgs()))
outdir.mkdir(parents=True, exist_ok=True)
expected_sha = "79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06"
if str(currentProgram.getExecutableSHA256()).lower() != expected_sha:
    raise ValueError("wrong executable SHA256")
if str(currentProgram.getLanguageID()) != "AARCH64:LE:64:v8A":
    raise ValueError("wrong SLEIGH language")
currentProgram.setImageBase(toAddr(0x100000), True)
comparisons = []
for name in ("div", "ldiv", "ffs", "ffsl", "ffsll", "swab"):
    text = (repo/f"Examples/claude/{name}_arm8.v").read_text()
    for addr, expected in re.findall(r"\(\* (0x[0-9a-f]+): (.*?) \*\)", text):
        address = toAddr(int(addr, 16))
        disassemble(address)
        insn = getInstructionAt(address)
        actual = str(insn) if insn is not None else None
        comparisons.append(dict(function=name, ghidra_address=addr, expected=expected, actual=actual,
                                bytes=bytes((int(b) & 255) for b in insn.getBytes()).hex() if insn else None,
                                match=actual == expected))
(outdir/"ghidra-audit.json").write_text(json.dumps(comparisons, indent=2)+"\n")
if not all(c["match"] for c in comparisons):
    raise ValueError("historical instruction comment mismatch; inspect ghidra-audit.json")
print(f"E02 PASS {len(comparisons)} exact historical instruction comments")

# The repository library is pinned by the enclosing Picinae commit and blobs.
sys.path.insert(0, str(repo/"tools/ghidra-lifter"))
for filename, expected in {
    "pcode2coq_lib.py": "c8222d7d4f5574af96fa33e7ec15de9aa8de5f64f5db127341cddcfa4ff742c5",
    "translationConstants.py": "da9fb47098746dca7efa227c1d7f1962a4fea43fad19c67944a24c031683d624",
}.items():
    if hashlib.sha256((repo/"tools/ghidra-lifter"/filename).read_bytes()).hexdigest() != expected:
        raise ValueError(f"smoke library pin mismatch: {filename}")
import pcode2coq_lib as lib
opts = argparse.Namespace(globalAddressing=False, interleave=False, typeCheck=True,
                          debugOps=False, strictFailure=True, staticMemory=False,
                          canonicalTemps=True, prependProgName=False)
text = (repo/"Examples/claude/toascii_arm8.v").read_text()
entry = int(re.search(r"entry: (0x[0-9a-f]+)", text)[1], 16)
info = lib.LiftInfo(entry, currentProgram.getLanguage(), opts, scriptobj=this)
original_vn_to_var = lib.vnToVar
temp_ids = {}


def canonical_vn_to_var(info, vn):
    if vn.isUnique():
        key = int(vn.getOffset())
        return f'(V_TEMP {temp_ids.setdefault(key, len(temp_ids))})'
    return original_vn_to_var(info, vn)


lib.vnToVar = canonical_vn_to_var
body = []
for offset, expected in ((0, "and w0,w0,#0x7f"), (4, "ret")):
    disassemble(toAddr(entry+offset))
    insn = getInstructionAt(toAddr(entry+offset))
    if insn is None or str(insn) != expected or insn.getLength() != 4:
        raise ValueError("restricted smoke instruction shape mismatch")
    temp_ids.clear()
    info.typctx = info.typctxBase.copy()
    body.append(lib.proc_insn(info, insn))
lift = f'''(* Restricted smoke adapter; pinned libc SHA256: {expected_sha}.
Ghidra 11.4.2; strictFailure=True; canonicalTemps per instruction.
No functional correctness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e02_toascii_smoke : program := fun _ a => match a with
{''.join(body)}
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e02_toascii_smoke.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
'''
(outdir/"e02_toascii_smoke.v").write_text(lift)
print("E02 wrote restricted toascii smoke lift")
