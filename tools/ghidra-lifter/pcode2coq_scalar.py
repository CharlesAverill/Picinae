"""Explicit strict AArch64 scalar replacement, not historical b7f0122 recovery.

Consume raw SLEIGH pcode (never decompiler high pcode). No fallback statements,
static memory hypotheses, or cross-instruction temporary state. See unit notes.
This module has no Java dependency; Ghidra supplies duck-typed varnodes/ops.
"""
import re


class Unsupported(ValueError):
    pass


def word(n, width):
    return f'Word 0x{n % (1 << width):x} {width}'


def cast(exp, src, dst, signed=False):
    if src == dst:
        return exp
    kind = 'LOW' if src > dst else 'SIGNED' if signed else 'UNSIGNED'
    return f'Cast CAST_{kind} {dst} ({exp})'


def binary(op, a, b):
    return f'BinOp OP_{op} ({a}) ({b})'


def seq(stmts):
    return ' $;\n\t'.join(stmts) if stmts else 'Nop'


BINARY = dict(INT_ADD='PLUS', INT_SUB='MINUS', INT_MULT='TIMES',
              INT_DIV='DIVIDE', INT_SDIV='SDIVIDE', INT_REM='MOD', INT_SREM='SMOD',
              INT_AND='AND', INT_OR='OR', INT_XOR='XOR', BOOL_AND='AND',
              BOOL_OR='OR', BOOL_XOR='XOR')
COMPARE = dict(INT_EQUAL='EQ', INT_NOTEQUAL='NEQ', INT_LESS='LT',
               INT_LESSEQUAL='LE', INT_SLESS='SLT', INT_SLESSEQUAL='SLE')
SHIFTS = dict(INT_LEFT='LSHIFT', INT_RIGHT='RSHIFT', INT_SRIGHT='ARSHIFT')
FLAGS = {'NG', 'ZR', 'CY', 'OV', 'TMPNG', 'TMPZR', 'TMPCY', 'TMPOV'}
# Instruction gate prevents empty or superficially scalar system/vector pcode
# from being accepted. Every pcode op and register is checked independently.
MNEMONICS = set('mov movk movz movn neg negs and ands orr eor bic cmp cmn tst '
                 'add adds sub subs mul msub madd sdiv udiv lsl lsr asr '
                 'adr adrp b cbz cbnz tbz tbnz cset csetm csel csinc csinv csneg '
                 'bfxil bfm ubfm sbfm ubfx sbfx uxtb uxth sxtb sxth sxtw '
                 'ldr ldrb ldrh ldrsw str strb strh ldur ldurb ldurh stur sturb sturh '
                 'ldp stp ret br bl nop clz rbit'.split())


class ScalarLifter:
    def __init__(self, language, base=0):
        if str(language.getLanguageID()) != 'AARCH64:LE:64:v8A':
            raise Unsupported('only AARCH64:LE:64:v8A is supported')
        self.lang = language
        self.base = base
        self.temps = {}
        self.ranges = []
        self.initialized = set()

    def register(self, vn):
        reg = self.lang.getRegister(vn.getAddress(), vn.getSize())
        if reg is None:
            raise Unsupported(f'unnamed register {vn}')
        base = reg.getBaseRegister()
        name = str(base.getName()).upper()
        if not (re.fullmatch(r'X(?:[0-9]|[12][0-9]|30)', name)
                or name in FLAGS | {'SP', 'PC'}):
            raise Unsupported(f'unmodeled register {reg} (base {base})')
        bw = int(base.getBitLength())
        width = int(vn.getSize()) * 8
        offset = (int(vn.getOffset()) - int(base.getAddress().getOffset())) * 8
        if offset < 0 or offset + width > bw or bw not in (8, 64):
            raise Unsupported(f'unsupported register slice {reg}')
        return f'R_{name}', bw, offset

    def temp(self, vn):
        offset, size = int(vn.getOffset()), int(vn.getSize())
        key = (offset, size)
        if key not in self.temps:
            if any(offset < b and a < offset + size for a, b in self.ranges):
                raise Unsupported('overlapping unique varnodes with distinct sizes')
            self.ranges.append((offset, offset + size))
            self.temps[key] = f'(V_TEMP {len(self.temps)})'
        return self.temps[key]

    def read(self, vn):
        width = int(vn.getSize()) * 8
        if width <= 0:
            raise Unsupported('zero-width varnode')
        if vn.isUnique():
            name = self.temp(vn)
            if name not in self.initialized:
                raise Unsupported(f'uninitialized instruction-local unique {vn}')
            return f'Var {name}', width
        if vn.isRegister():
            name, bw, offset = self.register(vn)
            exp = f'Var {name}'
            if width != bw:
                exp = f'Extract {offset + width - 1} {offset} ({exp})'
            return exp, width
        if vn.isConstant():
            return word(int(vn.getOffset()), width), width
        if vn.isAddress() and str(vn.getAddress().getAddressSpace().getName()) == 'ram':
            return f'Load (Var V_MEM64) ({word(int(vn.getOffset()), 64)}) LittleE {vn.getSize()}', width
        raise Unsupported(f'unmodeled varnode {vn}')

    def write(self, vn, exp, width):
        ow = int(vn.getSize()) * 8
        if width != ow:
            raise Unsupported(f'output width {width} != varnode width {ow}')
        if vn.isUnique():
            name = self.temp(vn)
            self.initialized.add(name)
        elif vn.isRegister():
            name, bw, offset = self.register(vn)
            if ow != bw:
                # Raw AArch64 SLEIGH emits explicit ZEXT W -> X. For any
                # partial write, merge exactly the addressed slice; do not
                # invent zero-extension for an arbitrary COPY/binop.
                mask = ((1 << bw) - 1) ^ (((1 << ow) - 1) << offset)
                new = cast(exp, ow, bw)
                if offset:
                    new = binary('LSHIFT', new, word(offset, bw))
                exp = binary('OR', binary('AND', f'Var {name}', word(mask, bw)), new)
        elif vn.isAddress() and str(vn.getAddress().getAddressSpace().getName()) == 'ram':
            return f'Move V_MEM64 (Store (Var V_MEM64) ({word(int(vn.getOffset()), 64)}) ({exp}) LittleE {vn.getSize()})'
        else:
            raise Unsupported(f'unmodeled output {vn}')
        return f'Move {name} ({exp})'

    def expression(self, op):
        code = str(op.getMnemonic())
        args = [self.read(v) for v in op.getInputs()]
        outwidth = int(op.getOutput().getSize()) * 8
        a, w = args[0]
        if code in BINARY or code in COMPARE:
            b, w2 = args[1]
            if w != w2:
                raise Unsupported(f'{code}: unequal input widths')
            if code in BINARY and outwidth != w:
                raise Unsupported(f'{code}: output width mismatch')
            exp = binary((BINARY | COMPARE)[code], a, b)
            return cast(exp, 1 if code in COMPARE else w, outwidth)
        if code in SHIFTS:
            if outwidth != w:
                raise Unsupported('shift output width mismatch')
            b, w2 = args[1]
            shifted = binary(SHIFTS[code], a, cast(b, w2, w))
            # Pcode shift count need not have the data width. Compare in
            # count width before truncation to preserve oversized shifts.
            if w2 > w:
                limit = binary('LT', b, word(w, w2))
                saturated = binary(SHIFTS[code], a, word(w, w))
                shifted = f'Ite ({limit}) ({shifted}) ({saturated})'
            return shifted
        if code == 'COPY':
            if w != outwidth:
                raise Unsupported('COPY width mismatch')
            return a
        if code in ('INT_ZEXT', 'INT_SEXT'):
            if w > outwidth:
                raise Unsupported('extension narrows')
            return cast(a, w, outwidth, code == 'INT_SEXT')
        if code == 'SUBPIECE':
            vn = op.getInputs()[1]
            if not vn.isConstant():
                raise Unsupported('nonconstant SUBPIECE')
            lo = int(vn.getOffset()) * 8
            if lo + outwidth > w:
                raise Unsupported('SUBPIECE outside input')
            return f'Extract {lo + outwidth - 1} {lo} ({a})'
        if code == 'PIECE':
            b, w2 = args[1]
            if w + w2 != outwidth:
                raise Unsupported('PIECE width mismatch')
            return f'Concat ({a}) ({b})'
        if code in ('INT_NEGATE', 'INT_2COMP', 'POPCOUNT'):
            op_name = dict(INT_NEGATE='NOT', INT_2COMP='NEG', POPCOUNT='POPCOUNT')[code]
            return cast(f'UnOp OP_{op_name} ({a})', w, outwidth)
        if code == 'BOOL_NEGATE':
            # Pcode boolean operands are normalized 0/1, including byte flags.
            return cast(binary('XOR', a, word(1, w)), w, outwidth)
        if code == 'LZCOUNT':
            # Picinae OP_BITWIDTH is N.size (0 -> 0), so CLZ(0)=w.
            return cast(binary('MINUS', word(w, w), f'UnOp OP_BITWIDTH ({a})'), w, outwidth)
        if code in ('INT_CARRY', 'INT_SCARRY', 'INT_SBORROW'):
            b, w2 = args[1]
            if w != w2:
                raise Unsupported('carry width mismatch')
            if code == 'INT_CARRY':
                exp = binary('LT', binary('PLUS', a, b), a)
            else:
                result = binary('PLUS' if code == 'INT_SCARRY' else 'MINUS', a, b)
                sign = lambda x: f'Extract {w - 1} {w - 1} ({x})'
                ab = binary('XOR', sign(a), sign(b))
                if code == 'INT_SCARRY':
                    ab = binary('XOR', ab, word(1, 1))
                exp = binary('AND', ab, binary('XOR', sign(a), sign(result)))
            return cast(exp, 1, outwidth)
        raise Unsupported(f'unmodeled op {code}')

    def statement(self, op):
        code = str(op.getMnemonic())
        ins = list(op.getInputs())
        arities = {**dict.fromkeys(BINARY | COMPARE | SHIFTS, 2),
                   **dict.fromkeys(('COPY','INT_ZEXT','INT_SEXT','INT_NEGATE','INT_2COMP','POPCOUNT','BOOL_NEGATE','LZCOUNT'),1),
                   **dict.fromkeys(('SUBPIECE','PIECE','INT_CARRY','INT_SCARRY','INT_SBORROW','LOAD'),2),
                   'STORE':3, 'BRANCHIND':1, 'RETURN':1}
        if code not in arities:
            raise Unsupported(f'unmodeled op {code}')
        if len(ins) != arities[code] or (op.getOutput() is None) != (code in ('STORE','BRANCHIND','RETURN')):
            raise Unsupported(f'malformed {code} pcode')
        if code in ('LOAD', 'STORE'):
            # Input 0 is an address-space ID, not a memory-valued expression.
            space = self.lang.getAddressFactory().getAddressSpace(int(ins[0].getOffset()))
            if space is None or str(space.getName()) != 'ram' or int(space.getSize()) != 64:
                raise Unsupported('nondefault memory space')
            addr, aw = self.read(ins[1])
            if aw != 64:
                raise Unsupported('memory address width != 64')
            if code == 'LOAD':
                out = op.getOutput()
                return self.write(out, f'Load (Var V_MEM64) ({addr}) LittleE {out.getSize()}', int(out.getSize()) * 8)
            data, _ = self.read(ins[2])
            return f'Move V_MEM64 (Store (Var V_MEM64) ({addr}) ({data}) LittleE {ins[2].getSize()})'
        if code in ('BRANCHIND', 'RETURN'):
            exp, w = self.read(ins[0])
            if w != 64:
                raise Unsupported('indirect jump width')
            return f'Jmp ({exp})'
        if code == 'CALLIND':
            raise Unsupported('indirect calls require separate boundary support')
        exp = self.expression(op)
        return self.write(op.getOutput(), exp, int(op.getOutput().getSize()) * 8)

    def instruction(self, insn):
        mnemonic = str(insn.getMnemonicString()).lower()
        if mnemonic not in MNEMONICS and not re.fullmatch(r'b\.(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)', mnemonic):
            raise Unsupported(f'unmodeled instruction {insn}')
        if int(insn.getLength()) != 4:
            raise Unsupported('non-A64 instruction length')
        ops = list(insn.getPcode())
        self.temps, self.ranges, self.initialized = {}, [], set()
        # Assign in deterministic first-use order, including branch operands.
        supported = set(BINARY) | set(COMPARE) | set(SHIFTS) | {
            'COPY','INT_ZEXT','INT_SEXT','INT_NEGATE','INT_2COMP','POPCOUNT',
            'BOOL_NEGATE','LZCOUNT','SUBPIECE','PIECE','INT_CARRY','INT_SCARRY',
            'INT_SBORROW','LOAD','STORE','BRANCHIND','RETURN','BRANCH','CBRANCH','CALL'}
        for op in ops:
            if str(op.getMnemonic()) not in supported:
                raise Unsupported(f'unmodeled op {op.getMnemonic()}')
            for vn in list(op.getInputs()) + [op.getOutput()]:
                if vn is not None and vn.isRegister():
                    self.register(vn)
            for vn in list(op.getInputs()) + [op.getOutput()]:
                if vn is not None and vn.isUnique():
                    self.temp(vn)
        if len(self.temps) >= 1000000:
            raise Unsupported('too many unique varnodes')
        if mnemonic == 'nop' and bytes((int(b) & 255) for b in insn.getBytes()) != bytes.fromhex('1f2003d5'):
            raise Unsupported('only the architectural NOP encoding is accepted, no hints/BTI')
        if not ops and mnemonic != 'nop':
            raise Unsupported('empty pcode for non-NOP instruction')
        if self.base and (insn.getFlowType().isCall() or mnemonic == 'bl'):
            raise Unsupported('calls require global addressing (absolute return addresses)')

        def block(start, stop, initialized):
            self.initialized = initialized.copy()
            stmts = []
            pc = start
            while pc < stop:
                op = ops[pc]
                code = str(op.getMnemonic())
                ins = list(op.getInputs())
                if code in ('BRANCH', 'CBRANCH', 'CALL'):
                    dest = ins[0]
                    cond = None
                    if code == 'CBRANCH':
                        c, w = self.read(ins[1])
                        cond = cast(c, w, 1)
                    if dest.isConstant():
                        if code == 'CALL':
                            raise Unsupported('intra-instruction CALL')
                        delta = int(dest.getOffset())
                        bits = int(dest.getSize()) * 8
                        if delta >= 1 << (bits - 1):
                            delta -= 1 << bits
                        target = pc + delta
                        if not pc < target <= stop:
                            raise Unsupported('backward/out-of-region pcode branch')
                        if cond is None:
                            pc = target
                            continue
                        before = self.initialized.copy()
                        skipped, after = block(pc + 1, target, before)
                        self.initialized = before & after
                        stmts.append(f'If ({cond}) (Nop) ({skipped})')
                        pc = target
                        continue
                    if not dest.isAddress() or str(dest.getAddress().getAddressSpace().getName()) != 'ram':
                        raise Unsupported('invalid direct jump destination')
                    target = word(int(dest.getOffset()) - self.base, 64)
                    jump = f'Jmp ({target})'
                    if cond is not None:
                        # A machine jump terminates this instruction on the
                        # taken path. Reject a trailing pcode suffix.
                        if pc + 1 != stop:
                            raise Unsupported('machine CBRANCH with trailing pcode')
                        stmts.append(f'If ({cond}) ({jump}) (Nop)')
                    else:
                        if pc + 1 != stop:
                            raise Unsupported('machine jump with trailing pcode')
                        stmts.append(jump)
                else:
                    stmts.append(self.statement(op))
                pc += 1
            return seq(stmts), self.initialized.copy()

        return block(0, len(ops), set())[0]
