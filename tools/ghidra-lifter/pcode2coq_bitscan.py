"""Guarded register-only AMD64 bit scans; exact pinned SLEIGH graphs.

No generic backward-edge translation. Missing feature declarations reject F3
aliases. Undefined destinations/flags are nondeterministic Picinae Unknowns.
"""
from pcode2coq_scalar import Unsupported, word, binary, cast, seq

SCANS = {'BSF', 'BSR', 'TZCNT', 'LZCNT'}
REGS = 'RAX RCX RDX RBX RSP RBP RSI RDI R8 R9 R10 R11 R12 R13 R14 R15'.split()


def encoding(insn):
    raw = bytes(int(b)&255 for b in insn.getBytes())
    if len(raw) != int(insn.getLength()):
        raise Unsupported('scan length mismatch')
    data = raw
    f3 = data[:1] == b'\xf3'
    if f3: data = data[1:]
    rex = 0
    if data and 0x40 <= data[0] <= 0x4f:
        rex, data = data[0], data[1:]
    if len(data) != 3 or data[0] != 0x0f or data[1] not in (0xbc,0xbd) or data[2] & 0xc0 != 0xc0 or rex & 2:
        raise Unsupported('scan requires exact 32/64-bit register encoding; prefixes/memory reject')
    mnemonic = ('TZCNT' if data[1] == 0xbc else 'LZCNT') if f3 else ('BSF' if data[1] == 0xbc else 'BSR')
    if str(insn.getMnemonicString()).upper() != mnemonic:
        raise Unsupported('scan mnemonic/encoding mismatch')
    width = 64 if rex & 8 else 32
    dst = REGS[((data[2] >> 3) & 7) + (8 if rex & 4 else 0)]
    src = REGS[(data[2] & 7) + (8 if rex & 1 else 0)]
    return mnemonic,width,'R_'+dst,'R_'+src


def expected_graph(mnemonic,w,dst,src):
    """Independent structural description, including all raw initializers/exits.

    Unique identities are canonical first-use numbers; widths remain exact.
    Constants retain byte size, including signed rel32 backward edges.
    """
    n=w//8
    C=lambda x,s=n: ('c',x,s)
    R=lambda name,s=n: ('r',name,s)
    U=lambda i,s=n: ('u',i,s)
    D,S,Z,F=R(dst),R(src),R('R_ZF',1),R('R_CF',1)
    op=lambda code,out,*args: (code,out,tuple(args))
    cb=lambda delta,cond: op('CBRANCH',None,C(delta,4),cond)
    br=lambda delta: op('BRANCH',None,C(delta % (1<<32),4))
    if mnemonic in ('BSF','BSR'):
        reverse=mnemonic=='BSR'
        graph=[op('COPY',U(0),C(w-1 if reverse else 0)),op('INT_EQUAL',Z,S,C(0)),
               op('INT_EQUAL',U(1,1),Z,C(1,1)),cb(6 if reverse else 7,U(1,1)),
               op('INT_RIGHT',U(2),S,U(0))]
        if reverse:
            graph += [op('INT_NOTEQUAL',U(3,1),U(2),C(0)),cb(3,U(3,1)),
                      op('INT_SUB',U(0),U(0),C(1)),br(-4)]
        else:
            graph += [op('INT_AND',U(3),U(2),C(1)),op('INT_NOTEQUAL',U(4,1),U(3),C(0)),
                      cb(3,U(4,1)),op('INT_ADD',U(0),U(0),C(1)),br(-5)]
        graph += [op('COPY',D,U(0))]
    elif mnemonic=='TZCNT':
        graph=[op('COPY',U(0),C(0)),op('COPY',U(1),S),op('INT_AND',U(2),U(1),C(1)),
               op('INT_NOTEQUAL',U(3,1),U(2),C(0)),cb(5,U(3,1)),op('INT_ADD',U(0),U(0),C(1)),
               op('INT_RIGHT',U(4),U(1),C(1,4)),op('INT_OR',U(1),U(4),C(1<<(w-1))),br(-6),
               op('INT_EQUAL',Z,U(0),C(0)),op('INT_EQUAL',F,S,C(0)),op('COPY',D,U(0))]
    else:
        # The pinned LZCNT graph reads SRC for CF after writing DST. When
        # aliased, that determinization is wrong: emitted IL snapshots SRC.
        graph=[op('LZCOUNT',D,S),op('INT_EQUAL',Z,D,C(0)),op('INT_EQUAL',F,S,C(0))]
    if w==32:
        graph += [op('INT_ZEXT',R(dst,8),D)]
    return graph


def lower(lifter,insn):
    mnemonic,w,dst,src=encoding(insn)
    effective=mnemonic
    if mnemonic in ('TZCNT','LZCNT'):
        feature=lifter.bmi1 if mnemonic=='TZCNT' else lifter.abm
        if feature not in ('present','absent'):
            raise Unsupported(mnemonic+' requires explicit CPU feature profile (present/absent)')
        if feature=='absent': effective='BSF' if mnemonic=='TZCNT' else 'BSR'
    lifter.temps,lifter.ranges,lifter.initialized={},[],set()
    def node(v):
        if v is None:return None
        size=int(v.getSize())
        if v.isConstant():return ('c',int(v.getOffset()) % (1 << (8*size)),size)
        if v.isUnique():
            name=lifter.temp(v)
            return ('u',int(name.split()[-1][:-1]),size)
        if v.isRegister():
            name,bw,off=lifter.register(v)
            if off or (bw==64 and size not in (4,8)):
                raise Unsupported('invalid scan register slice')
            return ('r',name,size)
        raise Unsupported('unexpected scan varnode')
    actual=[]
    for op in insn.getPcode():
        actual.append((str(op.getMnemonic()),node(op.getOutput()),tuple(node(v) for v in op.getInputs())))
    if actual != expected_graph(mnemonic,w,dst,src):
        raise Unsupported('unrecognized scan pcode graph (initialization/flags/loop/exits)')
    # All three temporaries are initialized before every use. Input and scan
    # cursor are distinct, so aliasing never changes flags' original operand.
    t=lambda i:f'(V_TEMP {i})'
    v=lambda i:f'Var {t(i)}'
    original = f'Var {src}' if w==64 else f'Extract 31 0 (Var {src})'
    leading=effective in ('BSR','LZCNT')
    bit=word(1<<(w-1) if leading else 1,w)
    advance=seq([f'Move {t(2)} ({binary("PLUS",v(2),word(1,w))})',
                 f'Move {t(1)} ({binary("LSHIFT" if leading else "RSHIFT",v(1),word(1,w))})'])
    keep=binary('AND',binary('LT',v(2),word(w,w)),binary('EQ',binary('AND',v(1),bit),word(0,w)))
    scan=f'Rep ({word(w,w)}) (If ({keep}) ({advance}) Nop)'
    result=binary('MINUS',word(w-1,w),v(2)) if effective=='BSR' else v(2)
    write=f'Move {dst} ({cast(result,w,64)})'
    zero=binary('EQ',v(0),word(0,w))
    if effective in ('BSF','BSR'):
        # Conservative full destination havoc for the undefined zero case.
        # In particular do not assert Ghidra's deterministic 0/w-1 result.
        write=f'If ({zero}) (Move {dst} (Unknown 64)) ({write})'
        flags=[f'Move R_ZF ({zero})', 'Move R_CF (Unknown 1)']
    else:
        flags=[f'Move R_ZF ({binary("EQ",v(2),word(0,w))})', f'Move R_CF ({zero})']
    return seq([f'Move {t(0)} ({original})',f'Move {t(1)} ({v(0)})',f'Move {t(2)} ({word(0,w)})',scan,
                *flags,write,*[f'Move R_{f} (Unknown 1)' for f in ('OF','SF','AF','PF')]])
