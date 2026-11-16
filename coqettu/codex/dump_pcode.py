#@category PCode
#@runtime PyGhidra
"""Dump one function's raw p-code for reviewing unsupported instructions."""
import json
from pathlib import Path

symbol, output_path = list(this.getScriptArgs())
functions = [f for f in currentProgram.getFunctionManager().getFunctionsNoStubs(True)
             if str(f.getName()) == symbol]
if len(functions) != 1:
    raise ValueError(f"Expected one function named {symbol}, found {len(functions)}")


def varnode(vn):
    if vn is None:
        return None
    return {"space": str(vn.getAddress().getAddressSpace().getName()),
            "offset": int(vn.getOffset()), "size": int(vn.getSize()), "text": str(vn)}


instructions = []
for instruction in currentProgram.getListing().getInstructions(functions[0].getBody(), True):
    instructions.append({
        "address": str(instruction.getAddress()), "assembly": str(instruction),
        "ops": [{"index": i, "mnemonic": str(op.getMnemonic()), "output": varnode(op.getOutput()),
                 "inputs": [varnode(vn) for vn in op.getInputs()]}
                for i, op in enumerate(instruction.getPcode())],
    })
destination = Path(output_path)
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(json.dumps({"function": symbol, "instructions": instructions}, indent=2) + "\n")
println(f"Written p-code dump: {destination}")
