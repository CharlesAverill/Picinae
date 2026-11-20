"""Strict AMD64 raw-pcode scalar profile. No decompiler or vector fallback.

Architectural GPR aliases and one-bit flags are checked independently of opcodes.
Addresses remain global, including RIP-relative data and CALL return addresses.
"""
import re
from pcode2coq_scalar import Unsupported, word, cast, binary, seq, BINARY, COMPARE, SHIFTS

GPRS = set('RAX RBX RCX RDX RSI RDI RSP RBP R8 R9 R10 R11 R12 R13 R14 R15'.split())
FLAGS = set('CF PF AF ZF SF OF DF'.split())
# Deliberately small instruction profile; opcode support alone grants nothing.
MNEMONICS = set('MOV MOVZX MOVSX MOVSXD LEA ADD SUB NEG NOT AND OR XOR CMP TEST '
                'CMOVZ CMOVNZ CMOVS CMOVNS SETZ SETNZ SETA SETBE SETL SETLE SETG SETGE '
                'JMP JZ JNZ JA JAE JB JBE JL JLE JG JGE JS JNS JO JNO JP JNP '
                'CALL RET PUSH POP'.split())
ARITIES = {**dict.fromkeys(BINARY | COMPARE | SHIFTS, 2),
           **dict.fromkeys(('COPY','INT_ZEXT','INT_SEXT','INT_NEGATE','INT_2COMP',
                            'BOOL_NEGATE','POPCOUNT'), 1),
           **dict.fromkeys(('SUBPIECE','PIECE','INT_CARRY','INT_SCARRY','INT_SBORROW','LOAD'),2),
           'STORE':3, 'BRANCH':1, 'CBRANCH':2, 'CALL':1, 'RETURN':1}
NO_OUTPUT = {'STORE','BRANCH','CBRANCH','CALL','RETURN'}
BOOL_OPS = set(COMPARE) | {'INT_CARRY','INT_SCARRY','INT_SBORROW','BOOL_NEGATE','BOOL_AND','BOOL_OR','BOOL_XOR'}


class X64Lifter:
    def __init__(self, language, cet_disabled=False):
        if str(language.getLanguageID()) != 'x86:LE:64:default':
            raise Unsupported('requires x86:LE:64:default')
        self.lang = language
        self.cet_disabled = cet_disabled
        self.temps, self.ranges, self.initialized = {}, [], set()

    def register(self, vn):
        reg = self.lang.getRegister(vn.getAddress(), vn.getSize())
        if reg is None:
            raise Unsupported(f'unknown register {vn}')
        base = reg.getBaseRegister()
        name = str(base.getName()).upper()
        size = int(vn.getSize())
        offset = (int(vn.getOffset()) - int(base.getAddress().getOffset())) * 8
        if name in FLAGS:
            if size != 1 or offset != 0 or str(reg.getName()).upper() != name:
                raise Unsupported('invalid flag slice')
            return f'R_{name}', 1, 0
        if name not in GPRS | {'RIP'} or int(base.getBitLength()) != 64:
            raise Unsupported(f'unmodeled register {reg} (base {base})')
        if (size, offset) not in ((8,0),(4,0),(2,0),(1,0),(1,8)):
            raise Unsupported(f'invalid register slice {reg}')
        if name in GPRS:
            legacy = {'RAX':('EAX','AX','AL','AH'),'RBX':('EBX','BX','BL','BH'),'RCX':('ECX','CX','CL','CH'),'RDX':('EDX','DX','DL','DH'),
                      'RSI':('ESI','SI','SIL',None),'RDI':('EDI','DI','DIL',None),'RSP':('ESP','SP','SPL',None),'RBP':('EBP','BP','BPL',None)}
            aliases = legacy.get(name,(name+'D',name+'W',name+'B',None))
            expected = {(8,0):name,(4,0):aliases[0],(2,0):aliases[1],(1,0):aliases[2],(1,8):aliases[3]}[(size,offset)]
            if str(reg.getName()).upper() != expected:
                raise Unsupported('unknown architectural register alias')
        if offset == 8 and name not in {'RAX','RBX','RCX','RDX'}:
            raise Unsupported('only legacy AH/BH/CH/DH high bytes')
        if name == 'RIP' and (size, offset) != (8,0):
            raise Unsupported('partial RIP')
        return f'R_{name}', 64, offset

    def temp(self, vn):
        off, size = int(vn.getOffset()), int(vn.getSize())
        if not 0 < size <= 16 or off < 0:
            raise Unsupported('invalid scalar unique width/offset')
        key = off, size
        if key not in self.temps:
            if any(off < b and a < off + size for a,b in self.ranges):
                raise Unsupported('overlapping unique varnodes')
            self.ranges.append((off, off+size))
            self.temps[key] = f'(V_TEMP {len(self.temps)})'
        return self.temps[key]

    def read(self, vn):
        w = int(vn.getSize()) * 8
        if w not in (8,16,32,64,128):
            raise Unsupported('invalid scalar varnode width')
        if vn.isUnique():
            name = self.temp(vn)
            if name not in self.initialized:
                raise Unsupported('uninitialized instruction-local unique')
            return f'Var {name}', w
        if vn.isRegister():
            name, bw, off = self.register(vn)
            if bw == 1:
                return cast(f'Var {name}', 1, 8), 8
            exp = f'Var {name}'
            return (f'Extract {off+w-1} {off} ({exp})' if w != bw else exp), w
        if vn.isConstant():
            return word(int(vn.getOffset()), w), w
        if vn.isAddress() and str(vn.getAddress().getAddressSpace().getName()) == 'ram':
            if w > 64:
                raise Unsupported('wide direct memory')
            return f'Load (Var V_MEM64) ({word(int(vn.getOffset()),64)}) LittleE {vn.getSize()}', w
        raise Unsupported(f'unmodeled varnode {vn}')

    def write(self, vn, exp, w):
        ow = int(vn.getSize()) * 8
        if w != ow or ow not in (8,16,32,64,128):
            raise Unsupported('output width mismatch')
        if vn.isUnique():
            name = self.temp(vn)
            self.initialized.add(name)
        elif vn.isRegister():
            name, bw, off = self.register(vn)
            if bw == 1:
                exp = cast(exp, ow, 1)
            elif ow == 32:
                # Intel SDM 3.4.1.1: every architectural r32 write clears high32.
                exp = cast(exp, 32, 64)
            elif ow != bw:
                mask = ((1<<64)-1) ^ (((1<<ow)-1)<<off)
                new = cast(exp, ow,64)
                if off:
                    new = binary('LSHIFT',new,word(off,64))
                exp = binary('OR',binary('AND',f'Var {name}',word(mask,64)),new)
        elif vn.isAddress() and str(vn.getAddress().getAddressSpace().getName()) == 'ram' and ow <= 64:
            return f'Move V_MEM64 (Store (Var V_MEM64) ({word(int(vn.getOffset()),64)}) ({exp}) LittleE {vn.getSize()})'
        else:
            raise Unsupported('unmodeled output varnode')
        return f'Move {name} ({exp})'

    def expression(self, op):
        code = str(op.getMnemonic())
        args = [self.read(v) for v in op.getInputs()]
        ow = int(op.getOutput().getSize())*8
        a,w = args[0]
        if code in BINARY or code in COMPARE:
            if code.startswith('BOOL_') and (w != 8 or ow != 8):
                raise Unsupported('boolean byte width required')
            b,w2 = args[1]
            if w != w2 or (code in BINARY and ow != w) or (code in COMPARE and ow != 8):
                raise Unsupported('binary/comparison width mismatch')
            return cast(binary((BINARY|COMPARE)[code],a,b),1 if code in COMPARE else w,ow)
        if code in SHIFTS:
            b,w2 = args[1]
            if ow != w:
                raise Unsupported('shift output width mismatch')
            exp = binary(SHIFTS[code],a,cast(b,w2,w))
            if w2 > w:
                exp = f'Ite ({binary("LT",b,word(w,w2))}) ({exp}) ({binary(SHIFTS[code],a,word(w,w))})'
            return exp
        if code == 'COPY':
            if w != ow:
                raise Unsupported('COPY width mismatch')
            return a
        if code in ('INT_ZEXT','INT_SEXT'):
            if w >= ow:
                raise Unsupported('extension must widen')
            return cast(a,w,ow,code=='INT_SEXT')
        if code == 'SUBPIECE':
            v = list(op.getInputs())[1]
            lo = int(v.getOffset())*8
            if not v.isConstant() or lo < 0 or lo+ow > w:
                raise Unsupported('invalid SUBPIECE')
            return f'Extract {lo+ow-1} {lo} ({a})'
        if code == 'PIECE':
            b,w2 = args[1]
            if w+w2 != ow:
                raise Unsupported('PIECE width mismatch')
            return f'Concat ({a}) ({b})'
        if code in ('INT_NEGATE','INT_2COMP','POPCOUNT'):
            if code != 'POPCOUNT' and w != ow:
                raise Unsupported('unary width mismatch')
            return cast(f'UnOp OP_{dict(INT_NEGATE="NOT",INT_2COMP="NEG",POPCOUNT="POPCOUNT")[code]} ({a})',w,ow)
        if code == 'BOOL_NEGATE':
            if w != 8 or ow != 8:
                raise Unsupported('boolean byte width required')
            return binary('XOR',a,word(1,8))
        if code in ('INT_CARRY','INT_SCARRY','INT_SBORROW'):
            b,w2 = args[1]
            if w != w2 or ow != 8:
                raise Unsupported('carry width mismatch')
            if code == 'INT_CARRY':
                exp = binary('LT',binary('PLUS',a,b),a)
            else:
                result = binary('PLUS' if code=='INT_SCARRY' else 'MINUS',a,b)
                sign = lambda x: f'Extract {w-1} {w-1} ({x})'
                ab = binary('XOR',sign(a),sign(b))
                if code == 'INT_SCARRY':
                    ab = binary('XOR',ab,word(1,1))
                exp = binary('AND',ab,binary('XOR',sign(a),sign(result)))
            return cast(exp,1,8)
        raise Unsupported(f'unmodeled op {code}')

    def shape(self, op):
        code, ins, out = str(op.getMnemonic()), list(op.getInputs()), op.getOutput()
        if code not in ARITIES:
            raise Unsupported(f'unmodeled op {code}')
        if len(ins) != ARITIES[code] or (out is None) != (code in NO_OUTPUT):
            raise Unsupported(f'malformed {code} pcode')
        return code, ins, out

    def statement(self, op):
        code, ins, out = self.shape(op)
        if code in ('LOAD','STORE'):
            if not ins[0].isConstant():
                raise Unsupported('nonconstant memory space ID')
            space = self.lang.getAddressFactory().getAddressSpace(int(ins[0].getOffset()))
            if space is None or str(space.getName()) != 'ram' or int(space.getSize()) != 64:
                raise Unsupported('nondefault memory space')
            addr,aw = self.read(ins[1])
            if aw != 64:
                raise Unsupported('memory address width !=64')
            if code=='LOAD':
                if int(out.getSize()) not in (1,2,4,8):
                    raise Unsupported('wide memory load')
                return self.write(out,f'Load (Var V_MEM64) ({addr}) LittleE {out.getSize()}',int(out.getSize())*8)
            data,w = self.read(ins[2])
            if w > 64:
                raise Unsupported('wide memory store')
            return f'Move V_MEM64 (Store (Var V_MEM64) ({addr}) ({data}) LittleE {ins[2].getSize()})'
        if code=='RETURN':
            exp,w = self.read(ins[0])
            if w != 64:
                raise Unsupported('return target width !=64')
            return f'Jmp ({exp})'
        if code in NO_OUTPUT:
            raise Unsupported('control op outside block')
        return self.write(out,self.expression(op),int(out.getSize())*8)

    def instruction(self, insn):
        mnemonic = str(insn.getMnemonicString()).upper()
        raw = bytes(int(b)&255 for b in insn.getBytes())
        if mnemonic == 'ENDBR64':
            if not self.cet_disabled or raw != bytes.fromhex('f30f1efa') or list(insn.getPcode()):
                raise Unsupported('ENDBR64 requires explicit CET-disabled profile and exact empty-pcode encoding')
            return 'Nop'
        if mnemonic not in MNEMONICS or not 1 <= int(insn.getLength()) <= 15:
            raise Unsupported(f'unmodeled instruction {insn}')
        # Reject all legacy prefixes except operand-size 66 and REX. Address-size,
        # segments, LOCK/REP, hints/CET/RTM are separate prerequisite profiles.
        for b in raw:
            if b in (0xf0,0xf2,0xf3,0x67,0x2e,0x36,0x3e,0x26,0x64,0x65):
                raise Unsupported('unsupported instruction prefix')
            if b != 0x66 and not 0x40 <= b <= 0x4f:
                break
        ops = list(insn.getPcode())
        self.temps,self.ranges,self.initialized = {},[],set()
        if not ops:
            raise Unsupported('empty pcode')
        for op in ops:
            code,ins,out = self.shape(op)
            for vn in ins+[out]:
                if vn is not None and vn.isRegister():
                    self.register(vn)
                if vn is not None and vn.isUnique():
                    self.temp(vn)
        flagop = 'INT_SCARRY' if mnemonic == 'ADD' else 'INT_SBORROW'
        if mnemonic in ('ADD','SUB','CMP','NEG') and sum(str(o.getMnemonic()) == flagop for o in ops) != 1:
            raise Unsupported('arithmetic shape lacks unique auxiliary-carry inputs')
        # Check unreachable operations too, with initialization checked precisely
        # below. No malformed dead suffix can escape the strict gate.
        self.initialized = set(self.temps.values())
        for index,op in enumerate(ops):
            code,ins,out = self.shape(op)
            if code in ('BRANCH','CBRANCH','CALL'):
                d = ins[0]
                if not d.isConstant() and not (d.isAddress() and str(d.getAddress().getAddressSpace().getName())=='ram'):
                    raise Unsupported('invalid branch destination')
                if d.isConstant():
                    bits = int(d.getSize())*8
                    if bits not in (8,16,32,64):
                        raise Unsupported('invalid pcode branch offset width')
                    delta = int(d.getOffset())
                    if delta >= 1 << (bits-1):
                        delta -= 1 << bits
                    if not index < index+delta <= len(ops):
                        raise Unsupported('backward/out-of-region pcode branch')
                elif code in ('BRANCH','CALL') and index+1 != len(ops):
                    raise Unsupported('unconditional machine branch with trailing pcode')
                if code=='CALL' and (mnemonic!='CALL' or raw[0]!=0xe8 or len(raw)!=5 or d.isConstant()):
                    raise Unsupported('only direct near E8 CALL supported')
                if code=='CBRANCH' and int(ins[1].getSize())!=1:
                    raise Unsupported('branch condition must be byte')
            else:
                if code=='RETURN' and (mnemonic!='RET' or index+1!=len(ops)):
                    raise Unsupported('invalid RETURN boundary')
                self.statement(op)
        def isreg(v,name):
            return v is not None and v.isRegister() and self.register(v) == (name,64,0) and int(v.getSize()) == 8
        def isconst(v,n):
            return v.isConstant() and int(v.getSize()) == 8 and int(v.getOffset()) == n
        if mnemonic == 'CALL':
            if len(ops)!=3 or [str(o.getMnemonic()) for o in ops] != ['INT_SUB','STORE','CALL']:
                raise Unsupported('unsupported CALL stack shape')
            _,sub,rsp = self.shape(ops[0])
            _,store,_ = self.shape(ops[1])
            _,target,_ = self.shape(ops[2])
            site = int(insn.getAddress().getOffset())
            relative = int.from_bytes(raw[1:],'little',signed=True)
            if not (isreg(rsp,'R_RSP') and isreg(sub[0],'R_RSP') and isconst(sub[1],8)
                    and isreg(store[1],'R_RSP') and isconst(store[2],site+5)
                    and int(target[0].getOffset()) == (site+5+relative) % (1<<64)):
                raise Unsupported('CALL lacks exact global return address/push/target')
        if mnemonic == 'RET':
            if raw != b'\xc3' or len(ops)!=3 or [str(o.getMnemonic()) for o in ops] != ['LOAD','INT_ADD','RETURN']:
                raise Unsupported('only exact near RET stack shape supported')
            _,load,rip = self.shape(ops[0])
            _,add,rsp = self.shape(ops[1])
            _,ret,_ = self.shape(ops[2])
            if not (isreg(rip,'R_RIP') and isreg(load[1],'R_RSP') and isreg(rsp,'R_RSP')
                    and isreg(add[0],'R_RSP') and isconst(add[1],8) and isreg(ret[0],'R_RIP')):
                raise Unsupported('RET lacks exact stack pop/return')

        def block(start,stop,initialized):
            self.initialized = initialized.copy()
            stmts,pc = [],start
            while pc < stop:
                op = ops[pc]
                code,ins,out = self.shape(op)
                if code in ('BRANCH','CBRANCH','CALL'):
                    dest,cond = ins[0],None
                    if code=='CBRANCH':
                        c,w = self.read(ins[1])
                        cond = binary('NEQ',c,word(0,w))
                    if dest.isConstant():
                        bits = int(dest.getSize())*8
                        delta = int(dest.getOffset())
                        if delta >= 1<<(bits-1):
                            delta -= 1<<bits
                        target = pc+delta
                        if code=='CALL' or not pc < target <= stop:
                            raise Unsupported('backward/out-of-region pcode branch')
                        if cond is None:
                            pc = target
                            continue
                        before = self.initialized.copy()
                        skipped,after = block(pc+1,target,before)
                        self.initialized = before & after
                        stmts.append(f'If ({cond}) (Nop) ({skipped})')
                        pc = target
                        continue
                    jump = f'Jmp ({word(int(dest.getOffset()),64)})'
                    if cond is not None:
                        # x64 CMOV uses a machine-address skip to the next
                        # instruction followed by a conditional pcode suffix.
                        rest,after = block(pc+1,stop,self.initialized)
                        stmts.append(f'If ({cond}) ({jump}) ({rest})')
                        return seq(stmts),after
                    if pc+1 != stop:
                        raise Unsupported('unconditional machine branch with trailing pcode')
                    stmts.append(jump)
                else:
                    if code=='RETURN' and pc+1!=stop:
                        raise Unsupported('RETURN with trailing pcode')
                    if mnemonic in ('ADD','SUB','CMP','NEG') and code == flagop:
                        # SLEIGH omits AF for these instructions. Intel defines
                        # it as carry/borrow across bit3; recover it before the
                        # raw operand is overwritten. Logical AF stays undefined.
                        a,w = self.read(ins[0])
                        b,w2 = self.read(ins[1])
                        result = binary('PLUS' if mnemonic=='ADD' else 'MINUS',a,b)
                        af = binary('XOR',binary('XOR',a,b),result)
                        stmts.append(f'Move R_AF (Extract 4 4 ({af}))')
                    stmts.append(self.statement(op))
                pc += 1
            return seq(stmts),self.initialized.copy()
        return block(0,len(ops),set())[0]
