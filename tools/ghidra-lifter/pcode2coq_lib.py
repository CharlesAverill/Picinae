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
import ghidra.app.util.demangler.DemanglerUtil as DemanglerUtil

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

# TODO: split up? this does more than just package sleigh objects and metadata
class LiftInfo:
  baseAddr : int
  lang : SleighLanguage
  vt : VarnodeTranslator
  space : AddrSpace
  spaceMod : int # addr space size
  memBits : int # word size
  endness : str
  picArch : str
  typctxPrefix : str
  typctx : dict
  typctxBase : dict
  reg_whitelist : list
  bitreg_list : list # 1-bit registers
  bytreg_list : list # 8-bit registers
  interleave : bool
  strictFailure : bool
  debugOps : bool
  typeCheck : bool
  prependProgName : bool
  scriptobj : GhidraScript

  def __init__(self, baseAddr, lang, args, scriptobj):
    self.baseAddr = baseAddr
    self.lang = lang
    self.vt = VarnodeTranslator(lang)
    self.space = lang.getDefaultSpace()
    self.spaceMod = (2**self.space.getSize())
    self.memBits = self.space.getAddressableUnitSize() * 8
    self.bytreg_list = []
    self.bitreg_list = []
    self.typctxBase = {}
    self.interleave = args.interleave
    self.strictFailure = args.strictFailure
    self.debugOps = args.debugOps
    self.typeCheck = args.typeCheck
    self.scriptobj = scriptobj
    if lang.isBigEndian():
      self.endness = 'BigE'
    else: # Assuming there's no "MiddleE" arches
      self.endness = 'LittleE'

    match lang.getLanguageID().getIdAsString():
      case 'AARCH64:LE:64:v8A':
        self.picArch = 'armv8'
        self.typctxPrefix = 'arm8'
        self.typctxBase = const.arm8typctx
        self.reg_whitelist = const.arm8_PicRegs
        self.bytreg_list = const.arm8_BytRegs
      case 'ARM:LE:32:v8':
        self.picArch = 'armv7'
        self.typctxPrefix = 'arm7'
        self.typctxBase = const.arm7typctx
        self.reg_whitelist = const.arm7_PicRegs
      case 'eBPF:LE:64:default':
        self.picArch = 'ebpf'
        self.typctxPrefix = 'ebpf'
        # TODO: Add ebpf type context
        self.reg_whitelist = const.ebpf_PicRegs
      case 'x86:LE:64:default':
        self.picArch = 'amd64'
        self.typctxPrefix = 'x64'
        self.typctxBase = const.amd64typctx
        self.reg_whitelist = const.amd64_PicRegs
        self.bitreg_list = const.amd64_BitRegs
      case 'x86:LE:32:default':
        self.picArch = 'i386'
        self.typctxPrefix = 'x86'
        self.typctxBase = const.i386typctx
        self.reg_whitelist = const.i386_PicRegs
        self.bitreg_list = const.i386_BitRegs
      case other_arch:
        raise ValueError(f'Unsupported Arch: {other_arch}')
    self.typctx = self.typctxBase.copy()

def write_smem_banner(s:str):
  s += '\n'
  s += '\n(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *'
  s += '\n *                                                         *'
  s += '\n *               Static Memory Hypotheses                  *'
  s += '\n *                                                         *'
  s += '\n * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)'
  return s

def write_welltyped_banner(s:str):
  s += '\n'
  s += '\n(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *'
  s += '\n *                                                         *'
  s += '\n *                  Well-typed Theorem                     *'
  s += '\n *                                                         *'
  s += '\n * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)'
  return s

# convert pcode varnode to picinae var
def vnToVar(info: LiftInfo, vn) -> str:
    if vn.isUnique():
      return f'(V_TEMP 0x{vnOffset(vn):x})'
    elif vn.isRegister():
      # DEBUG
      #vt = VarnodeTranslator(info.lang)
      #print(vn.toString())
      #print(vt.getRegister(vn).toString() + " " + vt.getRegister(vn).getAliases().toString())

      return f'R_{vn.toString(info.lang).upper()}'
    # FIXME: subregs may be true for isAddress()
    elif vn.isConstant() or vn.isAddress(): # assume const is an addr space id
      return f'V_MEM{info.space.getSize()}'
    else:
      raise ValueError(f'Cannot convert {vn} to Picinae variable')

def isBaseReg(info: LiftInfo, vn):
  vt = info.vt
  try:
    return vt.getRegister(vn).isBaseRegister()
  except:
    return False
def vnToBase(info: LiftInfo, vn) -> Varnode:
  # Assuming varnodes are aligned within their parent register at an
  # offset equal to their size, we subtract the size from the address
  # until we find a base register. We impose 2 sanity checks:
  #   1. Subtract only a finite number of times, equal to the size of the largest register in bytes.
  #   2. Double check the base register contains the argument register.
  if isBaseReg(info, vn) or vn.isUnique():
    return vn
  vn_addr=vn.getAddress()
  def newVn(addr,size):
    # We build a new address using the address of the argument
    # to make sure they live in the same address space (e.g. 'register')
    return Varnode(vn_addr.getNewAddress(addr),size)
  for i in range(2**7+1):
    base_addr = vn.offset - i * vn.size
    for p in range(7+1):
      maybe_base = newVn(base_addr, 2**p)
      if isBaseReg(info, maybe_base) and \
         base_addr <= vn.offset and base_addr + 2**p >= vn.offset + vn.size:
        return maybe_base
  print(f'(* DEBUG: Could not find base for {vn} *)')
  return vn

def vnWidth(info: LiftInfo, vn) -> int:
  """Width of the Picinae expression emitted for a varnode."""
  if vn.isUnique() or (vn.isRegister() and isBaseReg(info, vn)):
    return info.typctx.get(vnToVar(info, vn), vn.getSize() * 8)
  # Subregisters emit Extract; constants and loads use the varnode's size.
  return vn.getSize() * 8


# convert pcode varnode to picinae exp
def vnToExp(info: LiftInfo, vn, lhs_width=None) -> str:
    if vn.isUnique():
      if lhs_width is None:
        return f'Var {vnToVar(info, vn)}'
      elif lhs_width < vnWidth(info, vn):
        return f'Extract {lhs_width-1} 0 (Var {vnToVar(info, vn)})'
      elif lhs_width > vnWidth(info, vn):
        return f'Cast CAST_UNSIGNED {lhs_width} (Var {vnToVar(info, vn)})'
      else:
        return f'Var {vnToVar(info, vn)}'
    elif vn.isRegister():
      reg = info.vt.getRegister(vn)
      if reg and reg.isBaseRegister():
        return f'Var {vnToVar(info, vn)}'
      else:
        vnbase = vnToBase(info,vn)
        base_addr = vnbase.getOffset()
        vn_offset = vn.getAddress().subtract(base_addr).getOffset()
        high_bit = (vn_offset + vn.size) * 8 - 1
        low_bit = vn_offset * 8
        return f'Extract {high_bit} {low_bit} (Var {vnToVar(info,vnToBase(info,vn))})'
    elif vn.isConstant():
      w = vn.getSize() * 8 if lhs_width is None else lhs_width
      return f'Word 0x{vnOffset(vn):x} {w}'
    # FIXME: subregs may be true for isAddress()
    elif vn.isAddress(): # handles mem references
    # Picinae uses BYTEwidth for load/store sizes
      return f'Load (Var {vnToVar(info, vn)}) (Word 0x{vnOffset(vn):x} {info.space.getSize()}) {info.endness} {vn.getSize()}'
    else:
      raise ValueError(f'Cannot convert {vn} to Picinae expression')

def vnBitReg(info: LiftInfo, vn):
  return vnToVar(info,vn) in getattr(info, 'bitreg_list', [])

def binopWidth(info: LiftInfo, vn1, vn2, bitout: bool = False) -> int:
  w1, w2 = vnWidth(info, vn1), vnWidth(info, vn2)
  return 1 if bitout or w1 == 1 or w2 == 1 else w1


def binopOperands(info: LiftInfo, vn1, vn2, bitout: bool = False):
  """Give both operands the same width, preserving Picinae's one-bit flags."""
  w = binopWidth(info, vn1, vn2, bitout)
  def operand(vn):
    if vn.isConstant() and vnWidth(info, vn) <= w:
      return vnToExp(info, vn, lhs_width=w)
    exp = vnToExp(info, vn)
    width = vnWidth(info, vn)
    if width != w:
      cast = 'CAST_LOW' if width > w else 'CAST_UNSIGNED'
      return f'Cast {cast} {w} ({exp})'
    return exp
  return operand(vn1), operand(vn2), w


# converts pcode binops to picinae binops
def toBinopExp(info: LiftInfo, opConvert: dict, binop: PcodeOp, vn1, vn2, bitout:bool = False) -> str:
  exp1, exp2, _ = binopOperands(info, vn1, vn2, bitout)
  return f'BinOp {opConvert.get(binop)} ({exp1}) ({exp2})'


# Cast the expression to a single bit when writing to a bit register.
# TODO: change the var input to a varnode so mv_stmt can handle the logic of finding
# the base register and casting to its bitwidth.
def mv_stmt(var: str, exp: str, info:LiftInfo, cast_unsigned=None, cast_signed=None, cast_low=None, cast_high=None, w=None) -> str:
  if var in info.bitreg_list:
    info.typctx[var] = 1
    return f'Move {var} (Cast CAST_LOW 1 ({exp}))'
  if var in info.bytreg_list and w is not None and w < 8:
    cast_unsigned = 8
  if cast_unsigned is not None:
    info.typctx[var]=cast_unsigned
    return f'Move {var} (Cast CAST_UNSIGNED {cast_unsigned} ({exp}))'
  if cast_signed is not None:
    info.typctx[var]=cast_signed
    return f'Move {var} (Cast CAST_SIGNED {cast_signed} ({exp}))'
  if cast_low is not None:
    info.typctx[var]=cast_low
    return f'Move {var} (Cast CAST_LOW {cast_low} ({exp}))'
  if cast_high is not None:
    info.typctx[var]=cast_high
    return f'Move {var} (Cast CAST_HIGH {cast_high} ({exp}))'
  if w is None:
    raise ValueError(f'Missing expression width for {var}')
  info.typctx[var]=w
  return f'Move {var} ({exp})'


def abs_jmp_dest(info: LiftInfo, vn) -> str:
  if vn.isAddress(): #ram
  # varnode size for direct jumps (BRANCH, CALL) is irrelevant
  # use all bits to account for relative addressing wraparound
    return f'Word 0x{to_pic_addr(info, vnOffset(vn)):x} {info.space.getSize()}'
  elif vn.isConstant():
    # no current solution to model this behavior in picinae
    return ValueError("Relative pcode jump detected")
  else:
    raise ValueError("Invalid address space type for jmp dest.")


def jmp_stmt(exp: str) -> str:
  return f'Jmp ({exp})'

# given reg is in whitelisted registers for the picinae arch
def modeledReg(info: LiftInfo, regVn) -> bool:
  return vnToVar(info, regVn) in info.reg_whitelist


#Scarry and Sborrow use large, confusing expressions to calculate overflow conditions
#These are written to follow exactly the c++ code ghidra uses to emulate them.
#to improve readability and prevent bugs, effort has been made to structure the
#following functions to look analagous to their c++ counterparts:
def scarry_exp(info: LiftInfo, in1: Varnode, in2: Varnode) -> str:
  exp1, exp2, w = binopOperands(info, in1, in2)
  in1_exp, in2_exp = f'({exp1})', f'({exp2})'
  shift_amt = f'(Word {w-1} {w})'

  res = f'(BinOp OP_PLUS {in1_exp} {in2_exp})'

  a = f'(BinOp OP_AND (BinOp OP_RSHIFT {in1_exp} {shift_amt}) (Word 1 {w}))'
  b = f'(BinOp OP_AND (BinOp OP_RSHIFT {in2_exp} {shift_amt}) (Word 1 {w}))'
  r = f'(BinOp OP_AND (BinOp OP_RSHIFT {res} {shift_amt}) (Word 1 {w}))'

  r = f'(BinOp OP_XOR {r} {a})'
  a = f'(BinOp OP_XOR {a} {b})'
  a = f'(BinOp OP_XOR {a} (Word 1 {w}))'
  r = f'(BinOp OP_AND {r} {a})'

  #cast 1bit to 8bits to reflect the pcode semantics of a return value of size 1byte
  cast = 'CAST_UNSIGNED' if w < 8 else 'CAST_LOW'
  return f'Cast {cast} 8 {r}'


def sborrow_exp(info: LiftInfo, in1: Varnode, in2: Varnode) -> str:
  exp1, exp2, w = binopOperands(info, in1, in2)
  in1_exp, in2_exp = f'({exp1})', f'({exp2})'
  shift_amt = f'(Word {w-1} {w})'

  res = f'(BinOp OP_MINUS {in1_exp} {in2_exp})'

  a = f'(BinOp OP_AND (BinOp OP_RSHIFT {in1_exp} {shift_amt}) (Word 1 {w}))'
  b = f'(BinOp OP_AND (BinOp OP_RSHIFT {in2_exp} {shift_amt}) (Word 1 {w}))'
  r = f'(BinOp OP_AND (BinOp OP_RSHIFT {res} {shift_amt}) (Word 1 {w}))'

  a = f'(BinOp OP_XOR {a} {r})'
  r = f'(BinOp OP_XOR {r} {b})'
  r = f'(BinOp OP_XOR {r} (Word 1 {w}))'
  a = f'(BinOp OP_AND {a} {r})'

  #cast 1bit to 8bits to reflect the pcode semantics of a return value of size 1byte
  cast = 'CAST_UNSIGNED' if w < 8 else 'CAST_LOW'
  return f'Cast {cast} 8 {a}'


def to_stmt(info: LiftInfo, op) -> str:
  # Should we make the output register the base register in all cases?
  out = op.getOutput()
  ins = op.getInputs()

  badRegs = [vnToVar(info, vn) for vn in (list(ins) + [out]) if (vn and vn.isRegister() and not modeledReg(info, vnToBase(info, vn)))]

  if badRegs:
    # comma-separated bad registers
    csBadRegs = functools.reduce(lambda a, x: f'{a} {x}', badRegs, '')
    if (info.strictFailure):
      raise NotImplementedError(f'Unmodeled Regs:{csBadRegs}')
    else:
      return f'Nop (* Unmodeled Regs:{csBadRegs} *)'
  else:
    match op.getOpcode():
      # Jmp
      case PcodeOp.BRANCH \
      | PcodeOp.CALL:
        return jmp_stmt(abs_jmp_dest(info, ins[0]))
      case PcodeOp.CBRANCH:
        # pcode byte -> picinae bit. Bools in ghidra are either 0 or 1, so this is valid
        return f'If (Cast CAST_LOW 1 ({vnToExp(info, ins[1])})) (\n\t\t{jmp_stmt(abs_jmp_dest(info, ins[0]))}\n\t) (* else *) (\n\t\tNop\n\t)'
      case PcodeOp.BRANCHIND \
      | PcodeOp.CALLIND \
      | PcodeOp.RETURN:
        return jmp_stmt(vnToExp(info, ins[0]))

      # Memory Ops
      case PcodeOp.COPY:
        baseout = vnToBase(info, out)
        if out == baseout:
          print(f'PcodeOp.COPY inputs[0]:{op.inputs[0]}')
          return mv_stmt(vnToVar(info, out),
              vnToExp(info, op.inputs[0]), info, w=vnWidth(info, ins[0]))
        else :
          return mv_stmt(vnToVar(info, baseout),
              vnToExp(info, op.inputs[0]), info, cast_unsigned=8*baseout.getSize())

      case PcodeOp.LOAD:
        # NOTE: address spaces for input0, input1, and output could technically all differ
        # TODO: If available cast the address to the byte-width of the source varnode (memory we're loading from, ins[0])
        #   "The data in input1 is interpreted as an unsigned offset and should have the same size as the space referred to by the"
        load_addr_vn = vnToExp(info, ins[1])
        new_val = f'Load (Var {vnToVar(info, ins[0])}) ({load_addr_vn}) {info.endness} {out.getSize()}'
        # FIXME: Verify temporary variables in pcode are write-once, otherwise need more complicated logic
        # when writing to a temp variable to make sure Coq doesn't try to read it before it gets written to
        # otherwise it won't typecheck (the uninitialized temp variable won't have a bitwidth)
        if isBaseReg(info, out) or out.isUnique():
          return mv_stmt(vnToVar(info, out),
               # FIXME: old code. didn't handle unique, regs
               # f'Load (Var {vnToVar(info, ins[0])}) (Word {vnOffset(ins[1])} {info.space.getSize()}) {info.endness} {out.getSize()}')
               # FIXME: might be wrong for explicit addresses?
               # FIXME: factor out Cast into vnToExp subregister routines
               new_val, info, w=out.getSize()*8)
        else:
          #                   |-------------------------        combined_val         ---------------------|
          #                   |--------  shifted_subreg  ------|      |--------  masked_old_val  ---------|
          #                   | - new_val ---|    |-out.offset-|      |-    __    -|    |- zero_mask_exp -|
          # base register := (new_subreg_value <<  subreg_offset) .| (base_reg_value .&     subreg_mask   )
          base_reg = vnToBase(info,out)
          base_bytes = base_reg.size
          subreg_first_byte = out.offset - base_reg.offset
          subreg_last_byte = subreg_first_byte + out.size - 1
          zero_mask = ''.join(reversed(['00' if subreg_first_byte <= i <= subreg_last_byte else 'FF' for i in range(base_bytes)]))
          zero_mask_exp = f'Word 0x{zero_mask} {base_bytes * 8}'
          masked_old_val = f'BinOp OP_AND (Var {vnToVar(info, base_reg)}) ({zero_mask_exp})'
          cast_new_val = f'Cast CAST_UNSIGNED {base_bytes*8} ({new_val})'
          shifted_subreg = f'BinOp OP_LSHIFT ({cast_new_val}) (Word {subreg_first_byte*8} {base_bytes*8})'
          combined_val = f'BinOp OP_OR ({shifted_subreg}) ({masked_old_val})'
          return mv_stmt(vnToVar(info,base_reg), combined_val, info, w=base_bytes*8)
      case PcodeOp.STORE:
        return mv_stmt(vnToVar(info, ins[0]),
             # FIXME: might be wrong for explicit addresses?
             # FIXME: factor out Cast into vnToExp subregister routines
             f'Store (Var {vnToVar(info, ins[0])}) ({vnToExp(info, ins[1])}) (Cast CAST_UNSIGNED {ins[2].getSize()*8} ({vnToExp(info, ins[2])})) {info.endness} {ins[2].getSize()}',
             info, w=8*2**info.space.getSize())

      # Simple BinOps
      case binop if binop in const.simpBinopTrans:
        baseout = vnToBase(info, out)
        bitout = vnBitReg(info, out)
        if out == baseout:
          return mv_stmt(vnToVar(info, out),\
            toBinopExp(info, const.simpBinopTrans, binop, ins[0], ins[1], bitout=bitout),
            info, w=binopWidth(info, ins[0], ins[1], bitout))
        else :
          return mv_stmt(vnToVar(info, baseout),\
            toBinopExp(info, const.simpBinopTrans, binop, ins[0], ins[1]), info, cast_signed=8*baseout.getSize())

      # Comparisons produce one bit; byte-sized architecture flags need widening.
      case binop if binop in const.bitBinopTrans:
        binExp = toBinopExp(info, const.bitBinopTrans, binop, ins[0], ins[1])
        var_out = vnToVar(info, out)
        if var_out in info.bytreg_list:
          return mv_stmt(vnToVar(info, out), binExp, info, cast_unsigned=8)
        else:
          return mv_stmt(vnToVar(info, out), binExp, info, w=1)

      # Complex BinOps
      case PcodeOp.PIECE:
        out = vnToBase(info, out)
        return mv_stmt(vnToVar(info, out),
                 f'Concat ({vnToExp(info, ins[0])}) ({vnToExp(info, ins[1])})',
                 info, w=vnWidth(info, ins[0])+vnWidth(info, ins[1]))
      case PcodeOp.SUBPIECE:
        out = vnToBase(info, out)
        # rshiftsize = op.inputs[1].offset*8
        # rshiftwordsize = op.inputs[0].size*8
        # outsize = op.output.size*8
        # for Binop OP_RSHIFT to be well-typed, both operands need to be the same size.
        # Cast CAST_LOW <outsizeBits> (BinOp OP_RSHIFT <src data> <rshift> <rshiftwordsize>
        return mv_stmt(vnToVar(info, out),
                 f'BinOp OP_RSHIFT ({vnToExp(info, ins[0])}) (Word {vnOffset(ins[1])*8} {vnWidth(info, ins[0])})',
                 info, cast_low=out.getSize()*8)
      case PcodeOp.INT_CARRY:
        out = vnToBase(info, out)
        exp1, exp2, _ = binopOperands(info, ins[0], ins[1])
        # intOp = lambda x,y: f'BinOp OP_PLUS ({vnToExp(info, x)}) ({vnToExp(info, y)})'
        # return f'Cast CAST_UNSIGNED 8 (BinOp OP_LT ({intOp(op.inputs[0],op.inputs[1])}) ({vnToExp(info, op.inputs[0])}))'
        return mv_stmt(vnToVar(info, out),
                 f'BinOp OP_LT (BinOp OP_PLUS ({exp1}) ({exp2})) ({exp1})', info, cast_unsigned=8)
      case PcodeOp.INT_SCARRY:
        out = vnToBase(info, out)
        return mv_stmt(vnToVar(info, out),
                 scarry_exp(info, ins[0], ins[1]), info, w=8)
      case PcodeOp.INT_SBORROW:
        out = vnToBase(info, out)
        return mv_stmt(vnToVar(info, out),
                 sborrow_exp(info, ins[0], ins[1]), info, w=8)

      # UnOps
      # NOTE: some may require cast wrappings at some point?
      case PcodeOp.INT_ZEXT:
        #return f'Cast CAST_UNSIGNED {op.output.size*8} ({vnToExp(info, op.inputs[0])})'
        out = vnToBase(info, out)
        return mv_stmt(vnToVar(info, out),
                 vnToExp(info, ins[0]), info, cast_unsigned=out.getSize()*8)
      case PcodeOp.INT_SEXT:
        out = vnToBase(info, out)
        #return f'Cast CAST_SIGNED {op.output.size*8} ({vnToExp(info, op.inputs[0])})'
        return mv_stmt(vnToVar(info, out),
                 vnToExp(info, ins[0]), info, cast_signed=out.getSize()*8)
      case PcodeOp.POPCOUNT:
        out = vnToBase(info, out)
        #return f'Cast CAST_LOW {op.output.size*8} (UnOp OP_POPCOUNT ({vnToExp(info, op.inputs[0])}))'
        cast = 'cast_unsigned' if out.getSize()*8 > vnWidth(info, ins[0]) else 'cast_low'
        return mv_stmt(vnToVar(info, out),
                 f'UnOp OP_POPCOUNT ({vnToExp(info, ins[0])})', info, **{cast: out.getSize()*8})
      case PcodeOp.LZCOUNT:
        out = vnToBase(info, out)
        # defined in terms of popcount. lzcount = totalBits - popcount
        return mv_stmt(vnToVar(info, out),
                 f'BinOp OP_MINUS (Word {vnWidth(info, ins[0])} {vnWidth(info, ins[0])}) (UnOp OP_POPCOUNT ({vnToExp(info, ins[0])}))',
                 info, cast_unsigned=out.getSize()*8)
      case PcodeOp.INT_2COMP:
        out = vnToBase(info, out)
        #return f'UnOp OP_NEG ({vnToExp(info, op.inputs[0])})'
        return mv_stmt(vnToVar(info, out),
                 f'UnOp OP_NEG ({vnToExp(info, ins[0])})', info, w=vnWidth(info, ins[0]))
      case PcodeOp.INT_NEGATE | PcodeOp.BOOL_NEGATE:
        out = vnToBase(info, out)
        #return f'UnOp OP_NOT ({vnToExp(info, op.inputs[0])})'
        return mv_stmt(vnToVar(info, out),
                 f'UnOp OP_NOT ({vnToExp(info, ins[0])})', info, w=vnWidth(info, ins[0]))

      case _:
        if (info.strictFailure):
          raise NotImplementedError(f'Unmodeled Op: {op.getMnemonic()}')
        else:
          return f'Nop (* Unmodeled Op: {op.getMnemonic()} *)'

# format seq of stmts
def seq_str(info: LiftInfo, acc, op) -> str:
  debug_op = '' if not info.debugOps else f'\n\t(* {op} *)'
  return f'{acc} $;{debug_op}\n\t{to_stmt(info, op)}'


def stmts_str(info: LiftInfo, ops) -> str:
  if not ops:
    debug_op = '' if not info.debugOps else '\n\t(* No pcode op *)'
    return f'{debug_op}\n\tNop'

  # add $; to every stmt except first
  first_stmt = to_stmt(info, ops[0])
  first_str = f'\n\t{first_stmt}' if not info.debugOps else \
               f'\n\t(* {ops[0]} *)\n\t{first_stmt}'
  return first_str + functools.reduce(lambda acc, x: seq_str(info, acc, x), ops[1::], '')


# convert offset from hex to get python int
# why? dealing with Java BigInt's everywhere is not ideal. can't use vn.getOffset() because Jlong loses info
# can't convert JBigInt to PyInt because Jlong is what bridges the gap, which can only hold at most 2^63 - 1
def addrToInt(addr) -> int:
  return int(f'0x{addr.toString(False, False)}', 0)


def vnOffset(vn) -> int:
  return addrToInt(vn.getAddress())


# modular sub to rebase for relative addressing
# returns insnOff if baseAddr is 0 (if global addressing is toggled on)
def to_pic_addr(info: LiftInfo, insnOff: int) -> int:
  return (info.spaceMod + (insnOff % info.spaceMod) - (info.baseAddr % info.spaceMod)) % info.spaceMod


def proc_insn(info: LiftInfo, insn) -> str:
  # instruction metadata
  proto = insn.getPrototype()
  # marks undefined/external functions
  comment = ''

  # from GhidraSnippets https://github.com/HackOvert/GhidraSnippets
  #deol = DisplayableEol(insn, True, True, True, True, 5, True, True)
  #if deol.hasAutomatic():
    #ac = deol.getAutomaticComment()
    #comment = f'\t//{ac[0]}'

  # original assembly instruction and address comment
  hex_addr = insn.getMinAddress().toString("0x")
  pic_addr = to_pic_addr(info, insn.address.offset)
  addr_size = len(hex_addr)
  asm =  f'(* {hex_addr   }: {insn} *)\n'
  asm += f'(* {pic_addr:>{addr_size}}: {insn} *)'
  # address mapping
  mapping = f'| 0x{to_pic_addr(info, insn.address.offset) :x} =>'
  # pcode -> picinae IL
  picIL = f'Some ({proto.getLength()},{stmts_str(info, insn.getPcode())}\n)'

  return f'{asm}\n{mapping} {picIL}\n'


# Optionally returns a function that the instruction jumps to.
def insnJumpsToInnerLoc(insn, fm):
  for ref in insn.getReferencesFrom():
    if not ref.getReferenceType().isJump():
      continue
    target_addr = ref.getToAddress()
    target_func = fm.getFunctionContaining(target_addr)
    if (target_func is not None and
      target_addr != target_func.getEntryPoint()):
      return target_func
  return None

# Recursively lift functions that the function jumps to an internal point in.
# This comes from functions that run a special prelude before continuing with
# another function's body.  E.g., gmpn_add_nc using gmpn_add_n.
def liftFuncRec(prog, fm, func, info, blacklist: set) -> str:
  print(f'liftFuncRec: entered {func}')
  result = ''
  funcs = set()
  blacklist.add(func)
  for insn in prog.getListing().getInstructions(func.getBody(), True):
    opt_dest = insnJumpsToInnerLoc(insn,fm)
    print(f'liftFuncRec:{func}:{insn}    refs:{insn.getReferencesFrom()}    opt_dest:{opt_dest}')
    if opt_dest:
      funcs.add(opt_dest)
    result += (proc_insn(info, insn)) + '\n'
  # Reserve all discovered functions before recursing so each body is emitted once.
  newblacklist = blacklist.union(funcs)
  print(f'liftFuncRec: funcs: {funcs}')
  for f in funcs.difference(blacklist):
    result += liftFuncRec(prog, fm, f, info, newblacklist)
  return result

# return (generatedName, liftedFunctionString)
def liftFunc(prog, func, info) -> (str, str):
  # using underscores since coq doesn't like periods in prog name
  print(prog)
  info.typctx = info.typctxBase.copy()
  picProgName = (((prog.getName() + '_') if info.prependProgName else '') +\
          func.getName() + '_' +\
          info.picArch\
          ).replace('.', '_')

  # header
  result = '(* Automatically generated with pcode2coq\n'
  # lift metadata
  result += f'arch: {info.picArch}\n'
  result += f'file: {prog.getName()}\n'
  result += f'SHA256: {prog.getExecutableSHA256()}\n'
  result += f'function: {func.getName()}'
  result += '\n*)\n\n'
  # coq code
  result += f'Require Import Picinae_{info.picArch}.\n'
  result += 'Require Import NArith.\n'
  result += f'Require Import Picinae_numbers.\n'
  result += 'Require Import Lia.\n'
  result += 'Open Scope N.\n\n'
  # program def
  result += f'Definition {picProgName} : program := fun _ a => match a with\n\n'

  # translated pcode -> Picinae IL
  if (info.interleave):
    dis = PseudoDisassembler(prog)
    b = func.getBody()
    addr = b.getMinAddress().add(-15)
    while addr <= b.getMaxAddress():
      insn = dis.disassemble(addr)
      if insn is not None:
        result += (proc_insn(info,insn)) + '\n'
      addr = addr.next()
  else:
    result += liftFuncRec(prog,prog.getFunctionManager(), func, info, set())
    # for insn in prog.getListing().getInstructions(func.getBody(), True):
    #   result += (proc_insn(info, insn)) + '\n'

  # end program def
  result += '| _ => None\nend.'

  # static memory
  wrote_smem_banner = False
  combined_data = []
  smem_defs = []
  # combines data tuples of (addr, len (bytes), value (int))
  # loops twice because each added data can combine at most twice
  def combine_data(addr_len_val,ds):
    addr, len, val = addr_len_val
    added_interval = False
    for d in ds:
      daddr, dlen, dval = d
      if addr+len == daddr:
        ds.remove(d)
        val += dval << (8*len)
        len += dlen
        ds.append((addr,len,val))
        added_interval= True
        break
    for d in ds:
      daddr, dlen, dval = d
      if daddr+dlen==addr:
        if added_interval: ds.remove((addr,len,val))
        ds.remove(d)
        val = (val << (8*dlen)) + dval
        len += dlen
        ds.append((daddr,len,val))
        added_interval= True
        break
    if not added_interval:
      ds.append((addr,len,val))

  for insn in prog.getListing().getInstructions(func.getBody(), True):
    for ref in insn.getReferencesFrom():
      target_addr = ref.getToAddress()
      symbol = info.scriptobj.getSymbolAt(target_addr)
      if symbol and symbol.getName().startswith('DAT'):
        # unsure if target_addr is always same as symbol address
        addr = symbol.getAddress()
        dat = info.scriptobj.getDataAt(addr)
        if dat is None:
          continue
        elif not wrote_smem_banner:
          result=write_smem_banner(result)
          wrote_smem_banner = True
        try:
          length = len(dat.getBytes())
          if type(dat.getValue()) is ghidraScalar:
            defname = f'SM{addr}'
            # In Ghidra 11.2 UnsignedValue() can return the negative interpretation so we
            # apply 2's bit complement to reattain the unsigned value
            val = dat.getValue().getUnsignedValue()
            if val < 0:
                val = abs((val ^ 0xffffffffffffffff) + 1)
            result += f'\n\nDefinition {defname} (mem:N) : Prop := xnbits mem (0x{addr}*8) (8*{length}) = {hex(val)}.'
            smem_defs.append(defname)
            combine_data((addr.getOffset(),length,val),combined_data)
          else:
            print(f'Found data of unknown type <{typeof(dat.getValue())}> at addr <{addr}>')
        except:
            print(f"Failed for data {dat}")
  # Print the combined data for more readable/usable specifications
  # TODO: create a file to hold the shared automation definitions.
  if combined_data:
    result += '''
Theorem xbits_none:
  forall m a, xbits m a a = 0.
Proof.
  intros; unfold xbits. rewrite N.sub_diag, N.pow_0_r, N.mod_1_r; reflexivity.
Qed.

Local Ltac solve_equality :=
  let i := fresh "i" in
  apply N.bits_inj; intro i;
  repeat match goal with
  | H: xbits ?m ?lo ?hi = _ |- context[xbits ?m ?lo ?higher] =>
      idtac "Using " H;
      let Bound := fresh "Bound" in
      rewrite (xbits_split lo hi higher m), H; cbv -[N.shiftl xbits N.lor N.testbit];
      only 1:
      let len := eval cbv in (hi - lo) in
      destruct (N.lt_ge_cases i len) as [Bound|Bound]; rewrite N.lor_spec;[
      rewrite N.shiftl_spec_low, Bool.orb_false_r by lia; rewrite <-N.ltb_lt in Bound;
      destruct i as [|i];[reflexivity| repeat (cbv in Bound || discriminate Bound || (destruct i as [i|i|]; [ | |try reflexivity])) ]
      | replace (N.testbit _ _) with false at 1;[rewrite Bool.orb_false_l;
          rewrite N.shiftl_spec_high'; try lia;
          (* Reformat the big value and return `i-bound` to `i` *)
          match goal with
          | Bound: ?len <= i |- _ = N.testbit ?v i => rewrite <-(recompose_bytes len v), N.lor_spec, N.mod_pow2_bits_high, Bool.orb_false_l,
          N.shiftl_spec_high; cbv [N.shiftr Pos.iter N.div2]; try lia; remember (i-64) as i' eqn:Hi; clear Bound Hi i; rename i' into i
          end
        | symmetry; apply N.bits_above_log2, N.log2_lt_pow2; try lia;
          match goal with
          | B: ?lo <= ?i |- ?left < 2 ^ ?i => try apply (N.lt_le_trans left (2^lo) (2^i)); try apply N.pow_le_mono_r; try lia
          end
        ]
      ]
  end;[> idtac | discriminate ..]; rewrite xbits_none; reflexivity.
    '''
    result += f'\n\nDefinition SMCombined (mem:N) : Prop := {' /\\ '.join([f'xnbits mem ({hex(t[0])}*8) ({t[1]}*8) = {hex(t[2])}' for t in combined_data])}.'
    result += f'\n\nTheorem SMCorrect: forall (mem:N), {' -> '.join([f'{name} mem' for name in smem_defs])} -> SMCombined mem.\nProof.\n'
    result += '''  intros. cbv -[xbits] in *.
  repeat match goal with |- _ /\\ _ => split end.
  solve_equality.
Qed.
    '''

  # footer
  if (info.typeCheck):
    result = write_welltyped_banner(result)
    result += '\n\n'
    result += f'Theorem welltyped: welltyped_prog {info.typctxPrefix}typctx {picProgName}.\n'
    result += 'Proof. Picinae_typecheck. Qed.\n'

  return (picProgName, result)
