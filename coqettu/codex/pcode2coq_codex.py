#@category PCode
#@runtime PyGhidra
"""Codex-local strict lifter adapter; shared lifter files are left unchanged."""
import sys
from pathlib import Path

directory = Path(__file__).resolve().parent
sys.path.insert(0, str(directory))
sys.path.insert(0, str(directory / "lifter_base"))
import bsf_adapter
import pcode2coq_lib as lifting
import pcode2coq_headless as headless

original_stmts = lifting.stmts_str
original_lift = headless.liftFunc
adapted_count = 0


def record(vn):
    if vn is None:
        return None
    return {"space": str(vn.getAddress().getAddressSpace().getName()),
            "offset": int(vn.getOffset()), "size": int(vn.getSize())}


def statements(info, ops, next_address):
    global adapted_count
    graph = [{"mnemonic": str(op.getMnemonic()), "output": record(op.getOutput()),
              "inputs": [record(vn) for vn in op.getInputs()]} for op in ops]
    if info.picArch != "i386" or not bsf_adapter.is_bsf32(graph):
        return original_stmts(info, ops, next_address)
    adapted_count += 1
    prefix = original_stmts(info, ops[:3], next_address)
    body = original_stmts(info, ops[4:7], next_address)
    increment = lifting.to_stmt(info, ops[8])
    zero = lifting.vnToExp(info, ops[3].getInputs()[1])
    found = lifting.vnToExp(info, ops[7].getInputs()[1])
    suffix = lifting.to_stmt(info, ops[10])
    return (prefix + " $;\n\t(* Codex BSF32: exact graph, 32 guarded iterations. *)\n"
            f"\tIf (Cast CAST_LOW 1 ({zero})) (\n\t\tNop\n\t) (* else *) (\n"
            "\t\tRep (Word 32 32) (" + body + " $;\n"
            f"\t\tIf (Cast CAST_LOW 1 ({found})) (Nop) (* else *) ({increment})\n"
            "\t\t)\n\t) $;\n\t" + suffix)


def lift_with_provenance(*args):
    before = adapted_count
    name, text = original_lift(*args)
    if adapted_count != before:
        text = ("(* Codex-local BSF32 adapter: bsf_adapter.py + pcode2coq_codex.py.\n"
                "   Exact Ghidra graph; bounded guarded Rep; other loops remain rejected. *)\n" + text)
    return name, text


lifting.stmts_str = statements
headless.liftFunc = lift_with_provenance
headless.this = this
headless.currentProgram = currentProgram
headless.println = println
headless.main()
