#@category Picinae
#@runtime PyGhidra
# Print raw p-code of the instruction at each given (file-offset-based) hex address + Ghidra image base.
base = currentProgram.getImageBase().getOffset()
for a in getScriptArgs():
    addr = toAddr(int(a, 16) + base)
    ins = getInstructionAt(addr)
    if ins is None:
        disassemble(addr); ins = getInstructionAt(addr)
    print(f'@ {addr}: {ins}')
    for i, op in enumerate(ins.getPcode()):
        print(f'    {i}: {op}')
