#@category Picinae
#@runtime PyGhidra
#
# Headless driver for pcode2coq (git-softseclab.utdallas.edu, commit b7f0122).
# pcode2coq.py itself is GUI-oriented (it lifts the function under the cursor and
# prompts for options), so this script calls its library entry point directly.
#
# Usage:
#   pyghidraRun -H <projdir> <proj> -process <binary> -noanalysis \
#     -scriptPath <this dir> -postScript pcode2coq_headless.py \
#       <pcode2coq dir> <outdir> <func>[=<coqname>] ...
#
# Options passed to pcode2coq: relative addressing (entry point = 0),
# --strictFailure (abort on unmodeled registers/ops instead of emitting Nop),
# --typeCheck (append the welltyped theorem).

import sys
import argparse
import pathlib
import re

args = list(getScriptArgs())
p2c_dir, outdir, funcs = args[0], pathlib.Path(args[1]), args[2:]
sys.path.insert(0, p2c_dir)
from pcode2coq_lib import LiftInfo, liftFunc, proc_insn

opts = argparse.Namespace(globalAddressing=False, interleave=False,
                          typeCheck=True, debugOps=False, strictFailure=True,
                          staticMemory=False, canonicalTemps=True)

def find_func(fname):
    if fname.startswith('0x'):
        f = getFunctionContaining(toAddr(int(fname, 16)))
        if f is None:
            raise Exception(f'{fname}: no function at this address')
        return f
    fs = list(getGlobalFunctions(fname))
    if not fs:
        fs = [getFunctionAt(s.getAddress())
              for s in currentProgram.getSymbolTable().getSymbols(fname)]
        fs = [f for f in fs if f is not None]
    if len(fs) != 1:
        raise Exception(f'{fname}: expected exactly one function, found {len(fs)}')
    return fs[0]

# Several functions (f1+f2+...=coqname) are lifted into ONE program with global
# (Ghidra) addresses, so that direct calls between them resolve.
def lift_multi(fnames, coqname):
    info = LiftInfo(0, currentProgram.getLanguage(), opts, scriptobj=this)
    lang = info.picArch
    out = '(* Automatically generated with pcode2coq (multi-function, global addressing)\n'
    out += f'arch: {lang}\nfile: {currentProgram.getName()}\n'
    for fn in fnames:
        f = find_func(fn)
        out += f'function: {f.getName()} at 0x{f.getEntryPoint().getOffset():x}\n'
    out += '*)\n\n'
    out += f'Require Import Picinae_{lang}.\nRequire Import NArith.\nOpen Scope N.\n\n'
    out += f'Definition {coqname} : program := fun _ a => match a with\n\n'
    for fn in fnames:
        f = find_func(fn)
        out += f'(* ---- {f.getName()} ---- *)\n\n'
        for insn in currentProgram.getListing().getInstructions(f.getBody(), True):
            out += proc_insn(info, insn) + '\n'
    out += '| _ => None\nend.\n'
    out += f'\nTheorem welltyped: welltyped_prog {info.typctx}typctx {coqname}.\n'
    out += 'Proof. Picinae_typecheck. Qed.\n'
    return out

outdir.mkdir(parents=True, exist_ok=True)
for spec in funcs:
    fname, _, coqname = spec.partition('=')
    if '+' in fname:
        try:
            text = lift_multi([f for f in fname.split('+') if f], coqname)
        except Exception as e:
            print(f'pcode2coq_headless: FAILED {fname}: {e}')
            continue
        (outdir / f'{coqname}.v').write_text(text)
        print(f'pcode2coq_headless: wrote {outdir / (coqname + ".v")}')
        continue
    fs = list(getGlobalFunctions(fname))
    if not fs:
        # aliases (e.g. labs = imaxabs) share one Function named after another symbol
        fs = [getFunctionAt(s.getAddress())
              for s in currentProgram.getSymbolTable().getSymbols(fname)]
        fs = [f for f in fs if f is not None]
    if len(fs) != 1:
        raise Exception(f'{fname}: expected exactly one function, found {len(fs)}')
    func = fs[0]
    # Relative addressing rebases jump targets but not the return address that
    # CALL pushes, so functions with calls must be lifted globally (fn+=name).
    if any(i.getFlowType().isCall()
           for i in currentProgram.getListing().getInstructions(func.getBody(), True)):
        print(f'pcode2coq_headless: FAILED {fname}: contains CALL; use {fname}+={coqname or fname}')
        continue
    info = LiftInfo(func.getEntryPoint().getOffset(), currentProgram.getLanguage(),
                    opts, scriptobj=this)
    try:
        picName, text = liftFunc(currentProgram, func, info)
    except Exception as e:
        print(f'pcode2coq_headless: FAILED {fname}: {e}')
        continue
    if coqname:
        text = re.sub(r'\b' + re.escape(picName) + r'\b', coqname, text)
        picName = coqname
    entry = func.getEntryPoint().getOffset()
    text = text.replace('function: ' + func.getName(),
                        f'function: {func.getName()}\nentry: 0x{entry:x} (lifted with entry rebased to 0)', 1)
    (outdir / f'{picName}.v').write_text(text + '\n')
    print(f'pcode2coq_headless: wrote {outdir / (picName + ".v")}')
