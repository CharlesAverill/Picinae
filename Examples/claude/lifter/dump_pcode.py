#@category Picinae
#@runtime PyGhidra
# Print the raw p-code of each instruction of the named functions (debugging aid).
for fname in getScriptArgs():
    fs = list(getGlobalFunctions(fname))
    if not fs:
        fs = [getFunctionAt(s.getAddress()) for s in currentProgram.getSymbolTable().getSymbols(fname)]
    f = fs[0]
    print(f'== {fname} @ {f.getEntryPoint()}')
    for ins in currentProgram.getListing().getInstructions(f.getBody(), True):
        print(f'{ins.getAddress()}: {ins}')
        for i, op in enumerate(ins.getPcode()):
            print(f'    {i}: {op}')
