#!/usr/bin/env python3
"""Independent arithmetic oracle tests of emitted IL; no target execution.

The small parser/evaluator covers the emitted scalar expression language.
These executable checks are regression evidence, not a soundness theorem.
"""
import random
import re
import unittest
from pcode2coq_scalar import ScalarLifter, Unsupported


class Space:
    def getName(self): return 'ram'
    def getSize(self): return 64


class Addr:
    def __init__(self, offset): self.offset = offset
    def getOffset(self): return self.offset
    def getAddressSpace(self): return Space()


class VN:
    def __init__(self, kind, offset, size): self.kind, self.offset, self.size = kind, offset, size
    def isUnique(self): return self.kind == 'unique'
    def isRegister(self): return self.kind == 'register'
    def isConstant(self): return self.kind == 'constant'
    def isAddress(self): return self.kind == 'ram'
    def getOffset(self): return self.offset
    def getSize(self): return self.size
    def getAddress(self): return Addr(self.offset)


class Reg:
    def __init__(self, name, offset, width): self.name, self.offset, self.width = name, offset, width
    def getBaseRegister(self): return self
    def getName(self): return self.name
    def getBitLength(self): return self.width
    def getAddress(self): return Addr(self.offset)


class Language:
    def getLanguageID(self): return 'AARCH64:LE:64:v8A'
    def getRegister(self, addr, size):
        # Synthetic slices of X0; one explicitly unsupported register.
        return Reg('TPIDR_EL0',100,64) if addr.offset == 100 else Reg('X30',200,64) if addr.offset == 200 else Reg('X0',0,64)
    def getAddressFactory(self): return self
    def getAddressSpace(self, n): return Space() if n == 0 else None


class Op:
    def __init__(self, code, out, *args): self.code, self.out, self.args = code, out, args
    def getMnemonic(self): return self.code
    def getOutput(self): return self.out
    def getInputs(self): return self.args


class Insn:
    def __init__(self, mnemonic, *ops): self.mnemonic, self.ops = mnemonic, ops
    def getMnemonicString(self): return self.mnemonic
    def getLength(self): return 4
    def getPcode(self): return self.ops
    def getBytes(self): return bytes.fromhex('1f2003d5')
    def getFlowType(self): return self
    def isCall(self): return self.mnemonic == 'bl'


def parse(text):
    tokens = iter(re.findall(r'\$;|\(|\)|0x[0-9a-f]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*', text))
    ts = list(tokens)
    pos = 0
    def pop():
        nonlocal pos
        t = ts[pos]; pos += 1
        return t
    def var():
        token = pop()
        if token == '(':
            assert pop() == 'V_TEMP'
            name = 'T'+pop()
            assert pop() == ')'
            return name
        return token
    def exp():
        op = pop()
        if op == '(':
            result = exp(); assert pop() == ')'; return result
        if op == 'Word': return ('word', int(pop(), 0), int(pop(), 0))
        if op == 'Var': return ('var', var())
        if op == 'BinOp': return ('bin', pop(), exp(), exp())
        if op == 'UnOp': return ('un', pop(), exp())
        if op == 'Cast': return ('cast', pop(), int(pop(), 0), exp())
        if op == 'Extract': return ('extract', int(pop(), 0), int(pop(), 0), exp())
        if op == 'Concat': return ('concat', exp(), exp())
        if op == 'Ite': return ('ite', exp(), exp(), exp())
        if op in ('Load', 'Store'):
            args = [exp() for _ in range(2 if op == 'Load' else 3)]
            assert pop() == 'LittleE'
            return (op.lower(), *args, int(pop(), 0))
        raise AssertionError(f'unsupported test expression {op}')
    def stmt():
        token = pop()
        if token == '(':
            result = sequence(); assert pop() == ')'; return result
        if token == 'Nop': return ('nop',)
        if token == 'Move': return ('move', var(), exp())
        if token == 'Jmp': return ('jump', exp())
        if token == 'If': return ('if', exp(), stmt(), stmt())
        raise AssertionError(f'unsupported test statement {token}')
    def sequence():
        result = [stmt()]
        while pos < len(ts) and ts[pos] == '$;':
            pop(); result.append(stmt())
        return ('seq', result)
    result = sequence()
    assert pos == len(ts), ts[pos:]
    return result


def signed(x, w): return x - (1 << w) if x >> (w-1) else x


def evaluate(tree, state):
    op, *args = tree
    if op == 'word': return args[0] % (1 << args[1]), args[1]
    if op == 'var': return state[args[0]]
    if op == 'cast':
        kind, w, e = args; x, old = evaluate(e, state)
        if kind == 'CAST_SIGNED': x = signed(x, old)
        if kind == 'CAST_HIGH': x >>= old-w
        return x % (1 << w), w
    if op == 'extract':
        hi, lo, e = args; x, _ = evaluate(e, state)
        return (x >> lo) % (1 << (hi-lo+1)), hi-lo+1
    if op == 'concat':
        a, wa = evaluate(args[0], state); b, wb = evaluate(args[1], state)
        return (a << wb) | b, wa+wb
    if op == 'ite': return evaluate(args[1] if evaluate(args[0], state)[0] else args[2], state)
    if op == 'un':
        name, e = args; x, w = evaluate(e, state)
        x = dict(OP_NEG=lambda: -x, OP_NOT=lambda: ~x, OP_POPCOUNT=lambda: x.bit_count(), OP_BITWIDTH=lambda: x.bit_length())[name]()
        return x % (1 << w), w
    if op == 'bin':
        name, a, b = args; x, w = evaluate(a, state); y, wy = evaluate(b, state); assert w == wy
        ops = dict(OP_PLUS=lambda: x+y, OP_MINUS=lambda: x-y, OP_TIMES=lambda: x*y,
                   OP_AND=lambda: x & y, OP_OR=lambda: x | y, OP_XOR=lambda: x ^ y,
                   OP_LSHIFT=lambda: x << y if y < w else 0, OP_RSHIFT=lambda: x >> y,
                   OP_ARSHIFT=lambda: signed(x, w) >> y, OP_EQ=lambda: x == y,
                   OP_NEQ=lambda: x != y, OP_LT=lambda: x < y, OP_LE=lambda: x <= y,
                   OP_SLT=lambda: signed(x, w) < signed(y, w), OP_SLE=lambda: signed(x, w) <= signed(y, w),
                   OP_SDIVIDE=lambda: 0 if y == 0 else (abs(signed(x,w)) // abs(signed(y,w))) * (-1 if (signed(x,w)<0) != (signed(y,w)<0) else 1))
        r = int(ops[name]()); ow = 1 if name in {'OP_EQ','OP_NEQ','OP_LT','OP_LE','OP_SLT','OP_SLE'} else w
        return r % (1 << ow), ow
    if op == 'load':
        m, a, n = args; mem, _ = evaluate(m, state); address, _ = evaluate(a, state)
        return sum(mem.get(address+i, 0) << (8*i) for i in range(n)), 8*n
    if op == 'store':
        m, a, d, n = args; mem, _ = evaluate(m, state); address, _ = evaluate(a, state); data, _ = evaluate(d, state)
        result = mem.copy(); result.update({address+i: (data >> (8*i)) & 255 for i in range(n)})
        return result, 'memory'
    raise AssertionError(op)


def execute(tree, state):
    op, *args = tree
    if op == 'seq':
        for s in args[0]:
            jump = execute(s, state)
            if jump is not None: return jump
    elif op == 'move': state[args[0]] = evaluate(args[1], state)
    elif op == 'if': return execute(args[1] if evaluate(args[0], state)[0] else args[2], state)
    elif op == 'jump': return evaluate(args[0], state)[0]
    elif op != 'nop': raise AssertionError(op)


class Tests(unittest.TestCase):
    def setUp(self): self.l = ScalarLifter(Language())
    def emitted(self, op, state):
        self.l.temps, self.l.ranges, self.l.initialized = {}, [], set()
        text = self.l.statement(op); execute(parse(text), state); return state
    def test_bool_negate(self):
        for n in (0, 1):
            state = {}; self.emitted(Op('BOOL_NEGATE', VN('unique',0,1), VN('constant',n,1)),state)
            self.assertEqual(state['T0'], (1-n,8))
    def test_clz(self):
        rng = random.Random(11)
        for w in (8,32,64):
            for x in [0,1,(1<<w)-1]+[1<<i for i in range(w)]+[rng.getrandbits(w) for _ in range(500)]:
                state = {}; self.l.temps = {}; self.emitted(Op('LZCOUNT',VN('unique',0,w//8),VN('constant',x,w//8)),state)
                self.assertEqual(state['T0'], (w-x.bit_length(),w))
    def test_partial_merge_all_offsets(self):
        original = 0xfedcba9876543210
        for size in (1,2,4):
            for offset in range(9-size):
                if offset+size > 8: continue
                state = {'R_X0': (original,64)}
                self.emitted(Op('COPY',VN('register',offset,size),VN('constant',0xab,size)),state)
                mask = ((1<<(8*size))-1) << (8*offset)
                self.assertEqual(state['R_X0'][0], (original & ~mask) | (0xab << (8*offset)))
    def test_w_zext(self):
        state = {'R_X0': (0xffffffffffffffff,64)}
        self.emitted(Op('INT_ZEXT',VN('register',0,8),VN('constant',0x80000000,4)),state)
        self.assertEqual(state['R_X0'],(0x80000000,64))
    def test_carry_overflow(self):
        # Exhaust every byte pair, with mathematical signed range oracle.
        for x in range(256):
            for y in range(256):
                for code, expected in [('INT_CARRY',x+y>255),('INT_SCARRY',not -128<=signed(x,8)+signed(y,8)<=127),('INT_SBORROW',not -128<=signed(x,8)-signed(y,8)<=127)]:
                    state = {}; self.l.temps = {}
                    self.emitted(Op(code,VN('unique',0,1),VN('constant',x,1),VN('constant',y,1)),state)
                    self.assertEqual(state['T0'][0],int(expected))
    def test_shift_large_count(self):
        for count in (0,1,31,32,33,256,2**32):
            state = {}; self.l.temps = {}
            self.emitted(Op('INT_RIGHT',VN('unique',0,4),VN('constant',0xffffffff,4),VN('constant',count,8)),state)
            self.assertEqual(state['T0'][0],0xffffffff >> count)
    def test_memory(self):
        state = {'V_MEM64': ({0x1234:0xab},'memory')}
        self.emitted(Op('LOAD',VN('unique',0,1),VN('constant',0,4),VN('constant',0x1234,8)),state)
        self.assertEqual(state['T0'],(0xab,8))
        self.emitted(Op('STORE',None,VN('constant',0,4),VN('constant',0x1235,8),VN('constant',0xcd,1)),state)
        self.assertEqual(state['V_MEM64'][0],{0x1234:0xab,0x1235:0xcd})
        self.assertIn('0x1234 64',self.l.read(VN('ram',0x1234,1))[0])
    def test_instruction_canonical_and_local(self):
        def ins(offset): return Insn('mov',Op('COPY',VN('unique',offset,8),VN('constant',7,8)),Op('COPY',VN('register',0,8),VN('unique',offset,8)))
        self.assertEqual(self.l.instruction(ins(10)),self.l.instruction(ins(100)))
        with self.assertRaises(Unsupported): self.l.instruction(Insn('mov',Op('COPY',VN('register',0,8),VN('unique',100,8))))
    def test_forward_branch_and_call(self):
        for cond in (0,1):
            ops = [Op('COPY',VN('unique',0,8),VN('constant',7,8)),Op('CBRANCH',None,VN('constant',2,8),VN('constant',cond,1)),Op('COPY',VN('unique',0,8),VN('constant',9,8)),Op('COPY',VN('register',0,8),VN('unique',0,8))]
            state = {}; execute(parse(self.l.instruction(Insn('sdiv',*ops))),state)
            self.assertEqual(state['R_X0'][0],7 if cond else 9)
        call = Insn('bl',Op('COPY',VN('register',200,8),VN('constant',0x1238,8)),Op('CALL',None,VN('ram',0x4560,8)))
        state = {}; jump=execute(parse(self.l.instruction(call)),state)
        self.assertEqual(jump,0x4560);self.assertEqual(state['R_X30'][0],0x1238)
        self.l.base=0x1000
        with self.assertRaises(Unsupported):self.l.instruction(call)
    def test_strict_rejections(self):
        for ins in [Insn('mrs'),Insn('dc'),Insn('ptrue'),Insn('bti'),Insn('mov',Op('COPY',VN('register',100,8),VN('constant',0,8))),Insn('mov',Op('FLOAT_ADD',VN('unique',0,8),VN('constant',0,8),VN('constant',0,8))),Insn('b',Op('BRANCH',None,VN('constant',0,8))),Insn('mov'),Insn('mov',Op('COPY',VN('unique',0,8),VN('constant',0,8)),Op('COPY',VN('unique',0,4),VN('constant',0,4)))]:
            with self.assertRaises(Unsupported,msg=str(ins.ops)):self.l.instruction(ins)


if __name__=='__main__': unittest.main(verbosity=2)
