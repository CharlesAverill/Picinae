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
BITFORMS = {'rev', 'ubfiz', 'orn', 'bics'}


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

    def check_bitform(self, insn, mnemonic, ops):
        """Accept only reviewed scalar encodings AND their exact SLEIGH DAG.

        e29: REV W/X, UBFIZ W/X (wrapping UBFM alias), unshifted ORN/BICS
        W/X, ordinary X0..X30 operands. Zero-register and shifted logical
        forms remain unsupported here. Lower the verified raw pcode through
        the existing operations below, preserving explicit ZEXT and NZCV.
        Unique offsets are irrelevant; opcode/order/width/constants/dataflow
        and all architectural reads/writes must match Ghidra 11.4.2.
        """
        raw = bytes(int(b) & 255 for b in insn.getBytes())
        if len(raw) != 4:
            raise Unsupported('bitform encoding length')
        bits = int.from_bytes(raw, 'little')
        sf = bits >> 31
        width, size = 32 << sf, 4 << sf
        rd, rn, rm = bits & 31, (bits >> 5) & 31, (bits >> 16) & 31
        if rd == 31 or rn == 31 or (mnemonic in {'orn', 'bics'} and rm == 31):
            raise Unsupported('bitform zero-register form is not covered')
        expected = []
        t = lambda i: ('t', i, size)
        r = lambda i, n=size: ('r', f'R_X{i}', 64, 0, n)
        c = lambda n, s=size: ('c', n, s)
        flag = lambda name: ('r', 'R_' + name, 8, 0, 1)
        def emit(code, out, *args):
            expected.append((code, out, tuple(args)))
        def result(code, *args):
            # The W form must end with an explicit full-X zero extension.
            emit(code, t(6) if not sf else r(rd), *args)
            if not sf:
                emit('INT_ZEXT', r(rd, 8), t(6))
        if mnemonic == 'rev':
            if bits & 0xfffffc00 != (0xdac00c00 if sf else 0x5ac00800):
                raise Unsupported('unhandled REV encoding')
            emit('COPY', t(0), r(rn))
            emit('INT_AND', t(1), t(0), c(0xff00ff00ff00ff00 if sf else 0xff00ff00))
            emit('INT_RIGHT', t(2), t(1), c(8, 4))
            emit('INT_AND', t(3), t(0), c(0x00ff00ff00ff00ff if sf else 0x00ff00ff))
            emit('INT_LEFT', t(4), t(3), c(8, 4))
            emit('INT_OR', t(0), t(2), t(4))
            if sf:
                emit('INT_AND', t(5), t(0), c(0xffff0000ffff0000))
                emit('INT_RIGHT', t(6), t(5), c(16, 4))
                emit('INT_AND', t(7), t(0), c(0x0000ffff0000ffff))
                emit('INT_LEFT', t(8), t(7), c(16, 4))
                emit('INT_OR', t(0), t(6), t(8))
                emit('INT_RIGHT', t(9), t(0), c(32, 4))
                emit('INT_LEFT', t(10), t(0), c(32, 4))
                emit('INT_OR', r(rd), t(9), t(10))
            else:
                emit('INT_RIGHT', t(5), t(0), c(16, 4))
                emit('INT_LEFT', t(6), t(0), c(16, 4))
                emit('INT_OR', t(0), t(5), t(6))
                emit('INT_ZEXT', r(rd, 8), t(0))
        elif mnemonic == 'ubfiz':
            immr, imms = (bits >> 16) & 63, (bits >> 10) & 63
            if (bits & 0xffc00000 != (0xd3400000 if sf else 0x53000000)
                    or not 0 <= imms < immr < width):
                raise Unsupported('unhandled UBFIZ encoding')
            lsb, field = width - immr, imms + 1
            emit('COPY', t(0), r(rn))
            emit('INT_RIGHT', t(1), t(0), c(immr))
            emit('INT_SUB', t(2), c(width), c(immr))
            emit('INT_LEFT', t(3), t(0), t(2))
            emit('INT_OR', t(4), t(1), t(3))
            emit('INT_AND', t(5), t(4), c(((1 << field) - 1) << lsb))
            result('INT_AND', t(5), c((1 << (lsb + field)) - 1))
        else:
            opcode = 0x2a200000 if mnemonic == 'orn' else 0x6a200000
            if bits & 0xffe0fc00 != opcode | (sf << 31):
                raise Unsupported('only unshifted scalar ORN/BICS is covered')
            emit('INT_2COMP', t(0), c(1))
            emit('INT_XOR', t(1), r(rm), t(0))
            if mnemonic == 'orn' and sf:
                emit('INT_OR', r(rd), r(rn), t(1))
            else:
                emit('INT_OR' if mnemonic == 'orn' else 'INT_AND', t(2), r(rn), t(1))
                if mnemonic == 'bics':
                    emit('INT_SLESS', flag('TMPNG'), t(2), c(0))
                    emit('INT_EQUAL', flag('TMPZR'), t(2), c(0))
                emit('COPY' if sf else 'INT_ZEXT', r(rd, 8), t(2))
                if mnemonic == 'bics':
                    emit('COPY', flag('NG'), flag('TMPNG'))
                    emit('COPY', flag('ZR'), flag('TMPZR'))
                    emit('COPY', flag('CY'), c(0, 1))
                    emit('COPY', flag('OV'), c(0, 1))

        temps = {}
        def node(v):
            if v is None:
                return None
            n = int(v.getSize())
            if v.isUnique():
                key = (int(v.getOffset()), n)
                return ('t', temps.setdefault(key, len(temps)), n)
            if v.isRegister():
                return ('r', *self.register(v), n)
            if v.isConstant():
                return ('c', int(v.getOffset()) % (1 << (8 * n)), n)
            raise Unsupported('non-scalar bitform varnode')
        actual = [(str(op.getMnemonic()), node(op.getOutput()), tuple(node(v) for v in op.getInputs())) for op in ops]
        if actual != expected:
            raise Unsupported('unhandled bitform raw-pcode shape')

    def conditional_compare(self, insn, ops):
        """Lower only the exact CCMP encoding and Ghidra 11.4.2 pcode shape.

        SLEIGH snapshots the OLD condition, installs all four fallback flags,
        then branches to inst_next on its negation, skipping a compare suffix.
        An ordinary machine CBRANCH cannot accept that trailing suffix. Match
        the entire DAG (including next address), then express just this shape
        as prefix; If(skip) Nop compare. No general CFG acceptance is added.
        NZCV and scratch flags remain modeled bytes containing boolean values.
        """
        raw = bytes(int(b) & 255 for b in insn.getBytes())
        if len(raw) != 4:
            raise Unsupported('CCMP encoding length')
        bits = int.from_bytes(raw, 'little')
        # sf/op/S/fixed fields, including reserved bits 10 and 4.
        if bits & 0x7fe00410 != 0x7a400000:
            raise Unsupported('unhandled CCMP encoding')
        sf, immediate = bits >> 31, (bits >> 11) & 1
        size = 4 << sf
        rn, operand = (bits >> 5) & 31, (bits >> 16) & 31
        cond, nzcv = (bits >> 12) & 15, bits & 15
        expected, names = [], {}
        def t(name, n=1):
            return ('t', names.setdefault(name, len(names)), n)
        def c(value, n=1): return ('c', value, n)
        def r(index): return ('r', f'R_X{index}', 64, 0, size)
        def f(name): return ('r', 'R_' + name, 8, 0, 1)
        def emit(code, out, *args): expected.append((code, out, tuple(args)))
        if cond < 8:
            value = f(('ZR', 'CY', 'NG', 'OV')[cond // 2])
            if cond & 1:
                emit('BOOL_NEGATE', t('condition'), value)
                value = t('condition')
        elif cond == 8:
            emit('BOOL_NEGATE', t('c0'), f('ZR'))
            emit('BOOL_AND', t('condition'), f('CY'), t('c0'))
            value = t('condition')
        elif cond == 9:
            emit('BOOL_NEGATE', t('c0'), f('CY'))
            emit('BOOL_OR', t('condition'), t('c0'), f('ZR'))
            value = t('condition')
        elif cond in (10, 11):
            emit('INT_EQUAL' if cond == 10 else 'INT_NOTEQUAL', t('condition'), f('NG'), f('OV'))
            value = t('condition')
        elif cond == 12:
            emit('BOOL_NEGATE', t('c0'), f('ZR'))
            emit('INT_EQUAL', t('c1'), f('NG'), f('OV'))
            emit('BOOL_AND', t('condition'), t('c0'), t('c1'))
            value = t('condition')
        elif cond == 13:
            emit('INT_NOTEQUAL', t('c0'), f('NG'), f('OV'))
            emit('BOOL_OR', t('condition'), f('ZR'), t('c0'))
            value = t('condition')
        else:
            value = c(1)  # Both AL and NV are always true in A64.
        # SLEIGH expands zero-register reads before the condition snapshot.
        if not immediate and operand == 31 and not sf:
            emit('COPY', t('rm', size), c(0, size))
        if rn == 31:
            emit('COPY', t('rn', size), c(0, size))
        a = t('rn', size) if rn == 31 else r(rn)
        b = c(operand, 4) if immediate else (c(0, size) if sf else t('rm', size)) if operand == 31 else r(operand)
        emit('COPY', t('saved'), value)
        emit('COPY', t('fallback'), c(nzcv))
        for name, mask in zip(('NG', 'ZR', 'CY', 'OV'), (8, 4, 2, 1)):
            emit('INT_AND', t(name), t('fallback'), c(mask))
            emit('INT_EQUAL', f(name), t(name), c(mask))
        emit('BOOL_NEGATE', t('skip'), t('saved'))
        branch = len(expected)
        next_address = (int(insn.getAddress().getOffset()) + 4) % (1 << 64)
        emit('CBRANCH', None, ('ram', next_address, 8), t('skip'))
        if immediate and sf:
            emit('INT_ZEXT', t('result', size), b)
            b = t('result', size)
        emit('INT_LESSEQUAL', f('TMPCY'), b, a)
        emit('INT_SBORROW', f('TMPOV'), a, b)
        emit('INT_SUB', t('result', size), a, b)
        emit('INT_SLESS', f('TMPNG'), t('result', size), c(0, size))
        emit('INT_EQUAL', f('TMPZR'), t('result', size), c(0, size))
        for name in ('NG', 'ZR', 'CY', 'OV'):
            emit('COPY', f(name), f('TMP' + name))

        temps = {}
        def node(v):
            if v is None: return None
            n = int(v.getSize())
            if v.isUnique():
                key = (int(v.getOffset()), n)
                return ('t', temps.setdefault(key, len(temps)), n)
            if v.isRegister(): return ('r', *self.register(v), n)
            if v.isConstant(): return ('c', int(v.getOffset()) % (1 << (8 * n)), n)
            if v.isAddress() and str(v.getAddress().getAddressSpace().getName()) == 'ram':
                return ('ram', int(v.getOffset()), n)
            raise Unsupported('non-scalar CCMP varnode')
        actual = [(str(op.getMnemonic()), node(op.getOutput()), tuple(node(v) for v in op.getInputs())) for op in ops]
        if actual != expected:
            raise Unsupported('unhandled CCMP raw-pcode shape')
        self.temps, self.ranges, self.initialized = {}, [], set()
        for op in ops:
            for vn in list(op.getInputs()) + [op.getOutput()]:
                if vn is not None and vn.isUnique(): self.temp(vn)
        prefix = [self.statement(op) for op in ops[:branch]]
        skip, width = self.read(ops[branch].getInputs()[1])
        suffix = seq([self.statement(op) for op in ops[branch + 1:]])
        return seq(prefix + [f'If ({cast(skip, width, 1)}) (Nop) ({suffix})'])

    def instruction(self, insn):
        mnemonic = str(insn.getMnemonicString()).lower()
        if mnemonic not in MNEMONICS | BITFORMS | {'ccmp'} and not re.fullmatch(r'b\.(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)', mnemonic):
            raise Unsupported(f'unmodeled instruction {insn}')
        if int(insn.getLength()) != 4:
            raise Unsupported('non-A64 instruction length')
        ops = list(insn.getPcode())
        if mnemonic == 'ccmp':
            return self.conditional_compare(insn, ops)
        if mnemonic in BITFORMS:
            self.check_bitform(insn, mnemonic, ops)
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
