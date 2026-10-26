#@category Picinae
#@runtime PyGhidra
# List the CALLOTHER (user-defined p-code op) names used by functions.
# Usage (headless postScript): list_userops.py FUN_0029d860 ...
from ghidra.program.model.pcode import PcodeOp
import collections
args = list(getScriptArgs())
lang = currentProgram.getLanguage()
for fname in args:
    fs = list(getGlobalFunctions(fname))
    if len(fs) != 1:
        print(f'list_userops: {fname}: {len(fs)} functions'); continue
    seen = collections.OrderedDict()
    for insn in currentProgram.getListing().getInstructions(fs[0].getBody(), True):
        for op in insn.getPcode():
            if op.getOpcode() == PcodeOp.CALLOTHER:
                name = lang.getUserDefinedOpName(int(op.getInput(0).getOffset()))
                seen.setdefault(name, set()).add(insn.getMnemonicString())
    print(f'list_userops: {fname}: ' + '; '.join(f'{k} [{",".join(sorted(v))}]' for k, v in seen.items()))
