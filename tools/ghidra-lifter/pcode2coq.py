#@author UTD-SL2lab
#@category PCode
#@keybinding
#@menupath
#@toolbar
#@runtime PyGhidra

# TODO: use consistent style. var names, spacing, calls
# TODO: better names

import java # jpype
import functools
import argparse
import pathlib
import logging
import sys
print(f'sys.version: {sys.version}')
import ghidra.app.util.demangler.DemanglerUtil as DemanglerUtil
from pcode2coq_lib import LiftInfo, liftFunc

# local
import translationConstants as const

# typing
# TODO: import more typing info
import ghidra.program.model.pcode.PcodeOp as PcodeOp
import ghidra.app.plugin.processors.sleigh.SleighLanguage as SleighLanguage
#import ghidra.app.util.DisplayableEol as DisplayableEol
import ghidra.program.model.address.AddressSpace as AddrSpace
import ghidra.program.model.pcode.Varnode as Varnode
import ghidra.program.model.pcode.VarnodeTranslator as VarnodeTranslator
from ghidra.program.model.scalar import Scalar as ghidraScalar
from ghidra.app.util import PseudoDisassembler

# Clear the console on every run
from ghidra.util import Msg
from ghidra.app.script import GhidraScript
from ghidra.app.services import ConsoleService
console = state.getTool().getService(ConsoleService)
if console:
    console.clearMessages()

def main():
  ap = argparse.ArgumentParser(prog='pcode2coq',
           description='transpile pcode to picinae IL')
  ap.add_argument('-s',
      '--symbol',
      nargs='?',
      help='specific symbol/function to lift')
  # NOTE: might be necessary for handling computed jumps and self-modifying code
  ap.add_argument('-g',
      '--globalAddressing',
      action='store_true',
      help='use global instead of relative addressing')
  ap.add_argument('-t',
      '--typeCheck',
      action='store_true',
      help='append picinae program welltyped proof for testing')
  ap.add_argument('-f',
      '--strictFailure',
      action='store_true',
      help='do not comment out statements containing unmodeled registers/operations. strictly fail on the first found instance of an unmodeled register/op')
  ap.add_argument('-i',
      '--interleave',
      action='store_true',
      help='disassemble the instructions at every byte offset')
  ap.add_argument('-p',
      '--debugOps',
      action='store_true',
      help='print pcode ops comments before every statement')
  ap.add_argument('-a',
      '--liftAll',
      action='store_true',
      help='lift all functions in the file; otherwise lift only the selected file (in interactive mode) or the symbol (in headless mode)')
  ap.add_argument('-v',
      '--saveOptions',
      action='store_true',
      help='save option settings for future interactive runs in `liftoptions.json`')
  ap.add_argument('-r',
      '--functionRegex',
        action='store',
        help='lift all files matching the regex')
  #ap.add_argument('-o',
      #'--output',
      #nargs=1,
      #help='write to custom output file name in output')

  fm = currentProgram.getFunctionManager()
  selectedFunc = fm.getFunctionContaining(currentAddress)

  #TODO: support headless mode. differentiate and make CFG obvious
  # headless will fill in parse args based on dialog boxes
  # rest of the script will be the same for both gui/headless

  if isRunningHeadless():
    print("headless!")
  else:
    print("Not headless!")
    #if args.symbol: # lift single func
      #func = getGlobalFunctions(args.symbol)
    #else: # lift all funcs

      #args = ap.parse_args()
  #else: # gui mode
  optFilePath = pathlib.Path(str(pathlib.Path(__file__).parent.resolve()) + f'/liftoptions.json')
  used_optfile = False
  try:
    with open(optFilePath, 'r') as file:
      options = java.util.ArrayList([i.rstrip() for i in file])
      used_optfile = True
  except FileNotFoundError:
    options = askChoices(
      "Lift Options",
      "Script Settings:",
      java.util.ArrayList([
                '--globalAddressing',
                '--interleave',
                '--typeCheck',
                '--debugOps',
                '--strictFailure',
                '--liftAll',
                '--saveOptions']),
      java.util.ArrayList([
                "Use global addressing",
                "Create an interleaved (shingled) disassembly",
                "Debug: append typecheck theorem to .v output",
                "Debug: prepend each statement with the pcode operation",
                "Debug: strictly fail if any unmodeled registers/ops are encountered",
                "Lift all functions instead of just the selected one",
                "Save lift options for future runs"]))
    if options.contains('--saveOptions'):
      try:
        with open(optFilePath, 'w') as file:
          for i in options:
            file.write(f'{i}\n')
      except:
        traceback.format_exc()

  global args
  args = ap.parse_args(args=list(options))

  if (args.liftAll):
    # lift all funcs in program (in ascending order from entry point)
    targetFuncs = fm.getFunctionsNoStubs(True)
  else:
    targetFuncs = [selectedFunc]

  # lift target func(s)
  for func in targetFuncs:
    # setup metadata obj needed for lifting
    global info
    info = LiftInfo(
      0 if args.globalAddressing else addrToInt(func.getEntryPoint()),
      currentProgram.getLanguage(),
      args,
      scriptobj=this)

    # lift
    (picProgName, liftedResult) = liftFunc(currentProgram, func, info)

    # write to output dir in script directory
    # use autogenerated picinae program name for output file if none given
    outputFile = pathlib.Path(str(pathlib.Path(__file__).parent.resolve()) + f'/output/{picProgName}.v')
    outputFile.parent.mkdir(exist_ok=True, parents=True)
    outputFile.write_text(liftedResult)

  # only print to console if one func was selected
  # too much overhead at scale
  if len(list(targetFuncs)) == 1:
    print(liftedResult)

  print(f'\nWritten to:')
  print(f'{str(outputFile)}')
  if used_optfile:
    print(f'\nTo bring back the options window delete or rename the default options file at:\n{optFilePath}')

if __name__ == '__main__':
  main()
