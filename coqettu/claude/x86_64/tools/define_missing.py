# Ghidra (PyGhidra) post-script: define functions at exported symbols that
# Ghidra's analysis left without a function.  Usage (headless, not -readOnly):
#   -postScript define_missing.py name1 name2 ...
from ghidra.app.cmd.function import CreateFunctionCmd
args = getScriptArgs()
st = currentProgram.getSymbolTable()
fm = currentProgram.getFunctionManager()
for name in args:
    syms = list(st.getGlobalSymbols(name))
    if not syms:
        print("define_missing: no symbol %s" % name); continue
    addr = syms[0].getAddress()
    f = fm.getFunctionAt(addr)
    if f is not None:
        print("define_missing: %s already a function (%s)" % (name, f.getName())); continue
    disassemble(addr)
    cmd = CreateFunctionCmd(name, addr, None, ghidra.program.model.symbol.SourceType.USER_DEFINED)
    ok = cmd.applyTo(currentProgram)
    print("define_missing: %s at %s -> %s" % (name, addr, ok))
