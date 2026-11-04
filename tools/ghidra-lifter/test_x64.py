#!/usr/bin/env python3
"""Independent integer oracles and actual raw-pcode replay. No correctness proof."""
import copy
import importlib.util
import json
from pathlib import Path
import random
import tempfile
import unittest
from test_scalar import VN, Addr, Reg, Op, Space, parse, execute, signed
from pcode2coq_x64 import X64Lifter, Unsupported, GPRS, FLAGS

REPO = Path(__file__).resolve().parents[2]
ARTIFACTS = REPO/'Examples/claude/lifter'


class Slice(Reg):
    def __init__(self, d):
        super().__init__(d['register'],d['offset'],d['size']*8)
        self.base = Reg(d['base'],d['base_offset'],d['base_width'])
    def getBaseRegister(self): return self.base


class Language:
    def __init__(self, rows=()):
        self.regs = {}
        for row in rows:
            for o in row['ops']:
                for v in o['inputs']+[o['output']]:
                    if v and 'register' in v:
                        self.regs[v['offset'],v['size']] = Slice(v)
    def getLanguageID(self): return 'x86:LE:64:default'
    def getRegister(self, addr, size): return self.regs.get((addr.offset,size))
    def getAddressFactory(self): return self
    def getAddressSpace(self, n): return Space() if n in (0,433) else None
    def add(self,name,offset=0,size=8,base='RAX',base_offset=0,base_width=64):
        self.regs[offset,size] = Slice(dict(register=name,offset=offset,size=size,base=base,base_offset=base_offset,base_width=base_width))
        return VN('register',offset,size)


def node(d):
    if d is None: return None
    return VN({'const':'constant','unique':'unique','register':'register','ram':'ram'}[d['space']],d['offset'],d['size'])


class Insn:
    def __init__(self,mnemonic,*ops,raw=b'\x89\xc0',address=0x101000):
        self.mnemonic,self.ops,self.raw,self.address = mnemonic,ops,raw,address
    def getMnemonicString(self): return self.mnemonic
    def getPcode(self): return self.ops
    def getLength(self): return len(self.raw)
    def getBytes(self): return self.raw
    def getAddress(self): return Addr(self.address)


def instruction(row):
    ops = [Op(o['code'],node(o['output']),*[node(v) for v in o['inputs']]) for o in row['ops']]
    return Insn(row['assembly'].split()[0],*ops,raw=bytes.fromhex(row['bytes']),address=int(row['address'],16))


def state():
    return {**{'R_'+r:(0,64) for r in GPRS|{'RIP'}},**{'R_'+r:(0,1) for r in FLAGS},'V_MEM64':({},'memory')}


def load_rows(directory):
    rows = {}
    for p in sorted((ARTIFACTS/directory).glob('*.pcode.json')):
        for row in json.loads(p.read_text()): rows[int(row['address'],16)] = row
    return rows


def emitted_program(directory,cet=False):
    rows = load_rows(directory)
    lifter = X64Lifter(Language(rows.values()),cet_disabled=cet)
    result = {}
    for a,row in rows.items():
        text = lifter.instruction(instruction(row))
        result[a] = (len(bytes.fromhex(row['bytes'])),parse(text))
        # Independently compare re-emission against every published program.
        for p in (ARTIFACTS/directory).glob('*.v'):
            if f'| {a:#x} =>' in p.read_text():
                assert '\t'+text+'\n)' in p.read_text(),(p,row)
    return result


def run(program,pc,s,limit=100):
    for _ in range(limit):
        if pc not in program: return pc
        length,tree = program[pc]
        # IL instruction temps are instruction-local, including at RET boundaries.
        for k in list(s):
            if k.startswith('T'): del s[k]
        target = execute(tree,s)
        pc = pc+length if target is None else target
    raise AssertionError('bounded smoke execution did not exit')


class Tests(unittest.TestCase):
    def setUp(self):
        self.lang = Language()
        self.rax = self.lang.add('RAX')
        self.eax = self.lang.add('EAX',size=4)
        self.ax = self.lang.add('AX',size=2)
        self.al = self.lang.add('AL',size=1)
        self.ah = self.lang.add('AH',offset=1,size=1)
        self.cf = self.lang.add('CF',offset=0x200,size=1,base='CF',base_offset=0x200,base_width=8)
        self.l = X64Lifter(self.lang)
    def emitted(self,op,s=None):
        s = state() if s is None else s
        self.l.temps,self.l.ranges,self.l.initialized = {},[],set()
        execute(parse(self.l.statement(op)),s)
        return s
    def test_partial_register_and_r32_zero(self):
        rng = random.Random(25)
        for original in [0,(1<<64)-1]+[rng.getrandbits(64) for _ in range(100)]:
            for reg,width,shift in [(self.al,8,0),(self.ah,8,8),(self.ax,16,0),(self.eax,32,0),(self.rax,64,0)]:
                val = rng.getrandbits(width)
                s=state();s['R_RAX']=(original,64)
                self.emitted(Op('COPY',reg,VN('constant',val,width//8)),s)
                expected = val if width>=32 else (original & ~(((1<<width)-1)<<shift)) | (val<<shift)
                self.assertEqual(s['R_RAX'],(expected,64))
    def test_flag_byte_read_and_one_bit_write(self):
        for n in (0,1):
            s=state();s['R_CF']=(n,1)
            self.emitted(Op('BOOL_NEGATE',self.cf,self.cf),s)
            self.assertEqual(s['R_CF'],(1-n,1))
            self.assertEqual(self.l.read(self.cf)[1],8)
    def test_carry_and_signed_overflow(self):
        # Exhaust every byte pair; also randomized full-width signed limits.
        rng=random.Random(25)
        for w,pairs in [(8,((x,y) for x in range(256) for y in range(256))),
                        (32,[(rng.getrandbits(32),rng.getrandbits(32)) for _ in range(500)]),
                        (64,[(rng.getrandbits(64),rng.getrandbits(64)) for _ in range(500)])]:
            size=w//8
            for x,y in pairs:
                sx,sy=signed(x,w),signed(y,w)
                for code,expected in [('INT_CARRY',x+y>=(1<<w)),('INT_SCARRY',not -(1<<(w-1)) <= sx+sy < 1<<(w-1)),('INT_SBORROW',not -(1<<(w-1)) <= sx-sy < 1<<(w-1))]:
                    s=self.emitted(Op(code,VN('unique',0,1),VN('constant',x,size),VN('constant',y,size)))
                    self.assertEqual(s['T0'],(int(expected),8))
    def test_memory_above_32bits(self):
        a=0x123456789abc
        s=self.emitted(Op('STORE',None,VN('constant',0,8),VN('constant',a,8),VN('constant',0xfedcba9876543210,8)))
        self.emitted(Op('LOAD',self.rax,VN('constant',0,8),VN('constant',a,8)),s)
        self.assertEqual(s['R_RAX'],(0xfedcba9876543210,64))
        self.assertEqual(self.l.read(VN('ram',a,4))[1],32)
    def test_forward_pcode_branch_and_definite_initialization(self):
        t=VN('unique',10,8)
        for c in (0,1,2):
            ins=Insn('MOV',Op('COPY',t,VN('constant',7,8)),Op('CBRANCH',None,VN('constant',2,8),VN('constant',c,1)),Op('COPY',t,VN('constant',9,8)),Op('COPY',self.rax,t))
            s=state();execute(parse(self.l.instruction(ins)),s)
            self.assertEqual(s['R_RAX'][0],7 if c else 9)
        with self.assertRaisesRegex(Unsupported,'uninitialized'):
            self.l.instruction(Insn('MOV',Op('CBRANCH',None,VN('constant',2,8),VN('constant',1,1)),Op('COPY',t,VN('constant',7,8)),Op('COPY',self.rax,t)))
    def test_canonical_temps_and_instruction_reset(self):
        def ins(n):return Insn('MOV',Op('COPY',VN('unique',n,8),VN('constant',7,8)),Op('COPY',self.rax,VN('unique',n,8)))
        self.assertEqual(self.l.instruction(ins(10)),self.l.instruction(ins(100)))
        with self.assertRaises(Unsupported):self.l.instruction(Insn('MOV',Op('COPY',self.rax,VN('unique',100,8))))
    def test_strict_invalid_pcode_and_registers(self):
        unknown=self.lang.add('XMM0',offset=100,size=8,base='ZMM0',base_offset=100,base_width=512)
        invalid=self.lang.add('BAD',offset=4,size=4)
        badflag=self.lang.add('CF',offset=0x200,size=2,base='CF',base_offset=0x200,base_width=8)
        for ins in [Insn('MOV',Op('COPY',unknown,VN('constant',1,8))),Insn('MOV',Op('COPY',invalid,VN('constant',1,4))),Insn('MOV',Op('COPY',badflag,VN('constant',1,2))),
                    Insn('MOV',Op('CALLOTHER',None,VN('constant',1,4))),Insn('MOV',Op('LZCOUNT',self.eax,VN('constant',1,4))),
                    Insn('MOV',Op('COPY',VN('unique',0,8),VN('constant',0,8)),Op('COPY',VN('unique',4,4),VN('constant',0,4))),
                    Insn('MOV',Op('COPY',self.rax,VN('constant',0,4))),Insn('MOV'),
                    Insn('JMP',Op('BRANCH',None,VN('constant',0,8))),Insn('JMP',Op('BRANCH',None,VN('constant',255,1))),
                    Insn('JZ',Op('CBRANCH',None,VN('ram',0x1000,8))),
                    Insn('MOV',Op('LOAD',self.rax,VN('constant',0,8),VN('constant',0,4))),
                    Insn('JMP',Op('BRANCH',None,VN('ram',0x1000,8)),Op('COPY',self.rax,VN('constant',0,8))),
                    Insn('MOV',Op('BRANCHIND',None,self.rax)),Insn('CALL',Op('CALL',None,VN('ram',0x1234,8)),raw=bytes.fromhex('e800000000'))]:
            with self.assertRaises(Unsupported,msg=str(ins.ops)):self.l.instruction(ins)
    def test_strict_instruction_gate(self):
        for name,raw in [('ENDBR64','f30f1efa'),('NOP','90'),('BSF','0fbcc0'),('TZCNT','f30fbcc0'),('PXOR','660fefc0'),('MOVSB.REP','f3a4'),('XBEGIN','c7f800000000'),('LFENCE','0faee8'),('MOV','66f389c0')]:
            with self.assertRaises(Unsupported):self.l.instruction(Insn(name,raw=bytes.fromhex(raw)))
        self.assertEqual(X64Lifter(self.lang,True).instruction(Insn('ENDBR64',raw=bytes.fromhex('f30f1efa'))),'Nop')
    def test_glibc_actual_pcode_oracles(self):
        prog=emitted_program('x64_scalar_smoke',cet=True)
        receipt=json.loads((ARTIFACTS/'x64_scalar_smoke/SUCCESS.json').read_text())
        entries={r['symbol']:int(r['entry'],16) for r in receipt['records']}
        rng=random.Random(25)
        for x in [0,1,127,128,255,0x80000000,0xffffffff,1<<63,(1<<64)-1]+[rng.getrandbits(64) for _ in range(100)]:
            for name in entries:
                s=state();s['R_RDI']=(x,64);s['R_RSI']=(x if x&1 else x^1,64)
                s['R_RSP']=(0x1000000010,64)
                s['V_MEM64'][0].update({0x1000000010+i:(0xdeadbeef1234>>(8*i))&255 for i in range(8)})
                self.assertEqual(run(prog,entries[name],s),0xdeadbeef1234)
                self.assertEqual(s['R_RSP'],(0x1000000018,64))
                expected = {'toascii':x&127,'isascii':int((x&0xffffffff)<=127),
                            'abs':abs(signed(x&0xffffffff,32))&0xffffffff,
                            'labs':abs(signed(x,64))&((1<<64)-1),
                            'pthread_equal':int(bool(x&1))}[name]
                self.assertEqual(s['R_RAX'][0],expected,(name,x))
    def test_actual_call_partial_memory_and_address_shapes(self):
        rows=load_rows('x64_scalar_fixture')
        prog=emitted_program('x64_scalar_fixture')
        s=state();s['R_RDI']=(0xfedcba9876543210,64);s['R_RSI']=(0x1234567800,64);s['R_RSP']=(0x2000000000,64)
        s['V_MEM64'][0].update({0x2000000000+i:(0xabcdef0123>>(8*i))&255 for i in range(8)})
        # Initialize the actual RIP-relative data slot from the assembled ELF,
        # keeping code and data addresses in the same global coordinate system.
        sys_path = str(REPO/'Examples/claude/inventory/e01-x86-inventory')
        import sys
        sys.path.insert(0,sys_path)
        from inventory import ELF
        data_row=next(r for r in rows.values() if r['assembly'].startswith('MOV RCX'))
        slot=next(v for o in data_row['ops'] for v in o['inputs'] if v['space']=='ram')['offset']
        data=ELF(REPO/'notes/e25-x86-scalar-driver/fixture/scalar.so').read(slot-0x100000,8)
        self.assertEqual(int.from_bytes(data,'little'),0x1122334455667788)
        s['V_MEM64'][0].update({slot+i:b for i,b in enumerate(data)})
        # Inspect the actual call before running the rest: correct RIP-relative
        # target, decremented RSP and exact 64-bit return address bytes.
        a=next(a for a,r in rows.items() if r['assembly'].startswith('CALL'))
        callee=execute(prog[a][1],s)
        self.assertEqual(s['R_RSP'],(0x1ffffffff8,64))
        mem=s['V_MEM64'][0]
        self.assertEqual(sum(mem[0x1ffffffff8+i]<<(8*i) for i in range(8)),a+5)
        execute(prog[callee][1],s)
        for asm,expected in [('MOV AH',0xfedcba987654ab10),('MOV AX',0xfedcba9876541234),('MOV EAX',0x89abcdef)]:
            address=next(a for a,r in rows.items() if r['assembly'].startswith(asm))
            execute(prog[address][1],s)
            self.assertEqual(s['R_RAX'],(expected,64))
        self.assertEqual(run(prog,callee,s),0xabcdef0123)
        self.assertEqual(s['R_RSP'],(0x2000000008,64))
        self.assertEqual(s['R_RCX'],(0x1122334455667788,64))
        self.assertEqual(s['R_RDX'],((-0x89abcdef) % (1<<64),64))
        # Take the actual JE edge as well as the preceding untaken run.
        cmp_address=next(a for a,r in rows.items() if r['assembly'].startswith('CMP'))
        jump_address=next(a for a,r in rows.items() if r['assembly'].startswith('JZ'))
        s['R_RDX']=s['R_RCX']
        execute(prog[cmp_address][1],s)
        self.assertIsNotNone(execute(prog[jump_address][1],s))
        self.assertEqual(sum(s['V_MEM64'][0][0x1234567800+i]<<(8*i) for i in range(8)),0x89abcdef)
        # Corrupted stack semantics or return literal must never be accepted.
        call=instruction(rows[a]) if rows[a]['assembly'].startswith('CALL') else instruction(next(r for r in rows.values() if r['assembly'].startswith('CALL')))
        bad=copy.deepcopy(call)
        bad.ops[1].args[2].offset+=1
        with self.assertRaises(Unsupported):X64Lifter(Language(rows.values())).instruction(bad)
    def test_actual_add_sub_flags(self):
        rows=load_rows('x64_scalar_fixture')
        lang=Language(rows.values())
        for asm,w,subtract in [('ADD AL',8,False),('SUB AX',16,True)]:
            row=next(r for r in rows.values() if r['assembly'].startswith(asm))
            tree=parse(X64Lifter(lang).instruction(instruction(row)))
            for x in list(range(256))+[(1<<(w-1))-1,1<<(w-1),(1<<w)-1]:
                s=state();s['R_RAX']=(x,64);execute(tree,s)
                result=(x-1 if subtract else x+1) % (1<<w)
                self.assertEqual(s['R_RAX'][0]&((1<<w)-1),result)
                expected={'AF':int((x%16==0) if subtract else (x%16==15)),
                          'CF':int(x<1 if subtract else x+1 >= 1<<w),
                          'OF':int(not -(1<<(w-1)) <= signed(x,w)+(-1 if subtract else 1) < 1<<(w-1)),
                          'SF':int(bool(result&(1<<(w-1)))),'ZF':int(result==0),
                          'PF':int((result&255).bit_count()%2==0)}
                for flag,value in expected.items(): self.assertEqual(s['R_'+flag],(value,1),(asm,x,flag))

    def test_actual_auxiliary_flag(self):
        rows=load_rows('x64_scalar_smoke')
        row=next(r for r in rows.values() if r['assembly']=='NEG EAX')
        lifter=X64Lifter(Language(rows.values()),True)
        tree=parse(lifter.instruction(instruction(row)))
        for x in range(256):
            s=state();s['R_RAX']=(x,64);execute(tree,s)
            self.assertEqual(s['R_AF'],(int(x%16 != 0),1))
            self.assertEqual(s['R_CF'],(int(x != 0),1))


if __name__=='__main__': unittest.main(verbosity=2)
