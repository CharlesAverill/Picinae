# Print raw p-code of instructions at given addresses (Grok Bot / coqettu).
# @runtime PyGhidra
args = getScriptArgs()
for a in args:
    addr = toAddr(int(a, 16))
    ins = getInstructionAt(addr)
    print("INSN", a, ins)
    for op in ins.getPcode():
        print("   ", op)
