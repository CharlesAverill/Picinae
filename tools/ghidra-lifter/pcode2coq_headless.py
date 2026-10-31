#@author UTD-SL2lab
#@category PCode
#@runtime PyGhidra

"""Lift Ghidra functions to Picinae IL from a Ghidra headless script run.

Example:
  analyzeHeadless ... -postScript pcode2coq_headless.py --symbol main
"""

import argparse
import pathlib
import re

from pcode2coq_lib import LiftInfo, liftFunc
from pcode2coq_lib import addrToInt


def parse_args():
    parser = argparse.ArgumentParser(
        prog="pcode2coq_headless.py",
        description="Lift Ghidra functions to Picinae IL without a GUI.",
    )
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("-s", "--symbol", help="function name to lift")
    selection.add_argument("-r", "--functionRegex", help="regex matching function names to lift")
    selection.add_argument("-a", "--liftAll", action="store_true", help="lift every function")
    parser.add_argument("-g", "--globalAddressing", action="store_true",
                        help="use global instead of relative addressing")
    parser.add_argument("-t", "--typeCheck", action="store_true",
                        help="append Picinae program welltyped proof for testing")
    parser.add_argument("-f", "--strictFailure", action="store_true",
                        help="fail on unmodeled registers or operations")
    parser.add_argument("-i", "--interleave", action="store_true",
                        help="disassemble instructions at every byte offset")
    parser.add_argument("-p", "--debugOps", action="store_true",
                        help="print pcode ops comments before every statement")
    parser.add_argument("-o", "--outputDir", type=pathlib.Path,
                        help="directory for generated .v files (default: script-dir/output)")
    parser.add_argument("--prependProgName", action="store_true",
                        help="Prepend the file and function name with the program.")
    return parser.parse_args(list(this.getScriptArgs()))


def main():
    args = parse_args()
    function_manager = currentProgram.getFunctionManager()

    if args.liftAll:
        targets = list(function_manager.getFunctionsNoStubs(True))
    else:
        pattern = re.compile(args.functionRegex) if args.functionRegex else None
        targets = []
        for function in function_manager.getFunctionsNoStubs(True):
            name = str(function.getName())
            if (args.symbol is not None and name == args.symbol) or (
                pattern is not None and pattern.search(name)
            ):
                targets.append(function)
        if args.symbol and not targets:
            raise ValueError("No function found with name: {}".format(args.symbol))

    if not targets:
        raise ValueError("No functions matched the requested selection")

    output_dir = args.outputDir
    if output_dir is None:
        output_dir = pathlib.Path(str(pathlib.Path(__file__).parent.resolve())) / "output"
    output_dir.mkdir(exist_ok=True, parents=True)

    for function in targets:
        info = LiftInfo(
            0 if args.globalAddressing else addrToInt(function.getEntryPoint()),
            currentProgram.getLanguage(),
            args,
            scriptobj=this,
        )
        program_name, lifted_result = liftFunc(currentProgram, function, info)
        output_file = output_dir / (program_name + ".v")
        output_file.write_text(lifted_result)
        println("Written: {}".format(output_file))


if __name__ == "__main__":
    main()
