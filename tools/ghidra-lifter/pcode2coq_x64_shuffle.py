"""Opt-in legacy XMM128 PALIGNR, selected by the exact e01 copy census.

A deliberately small symbolic DAG gate, not an ISA soundness theorem. No new
PSHUFB, VEX, MMX, EVEX, userop or generic vector support is enabled here.
"""
from dataclasses import dataclass
from pcode2coq_x64 import Unsupported
from pcode2coq_x64_copy import CopyLifter, GPR, GPROFF, MASK, poly, add, require
from pcode2coq_scalar import binary, word


@dataclass(frozen=True)
class Align:
    dst: int
    src: int | None
    immediate: int
    address: tuple | None = None


def decode(raw, site):
    require(6 <= len(raw) <= 15 and raw[0] == 0x66, 'only legacy XMM128 PALIGNR')
    i=1; r=x=b=0; rex=None
    if 0x40 <= raw[i] <= 0x4f:
        rex=raw[i];i+=1
        require(rex&8 == 0 and rex!=0x40, 'REX.W/redundant REX outside shuffle profile')
        r=(rex>>2)&1;x=(rex>>1)&1;b=rex&1
    require(raw[i:i+3] == b'\x0f\x3a\x0f', 'unmodeled shuffle opcode/map/prefix')
    i+=3
    require(i+2 <= len(raw), 'missing ModRM/immediate')
    modrm=raw[i];i+=1
    mod=modrm>>6;dst=((modrm>>3)&7)+8*r;rm=modrm&7
    if mod==3:
        require(x==0, 'ignored REX.X outside register shuffle profile')
        require(i+1 == len(raw), 'trailing register encoding bytes')
        return Align(dst,rm+8*b,raw[-1])
    terms=[];disp=0;dispbytes=0
    if rm==4:
        require(i+2 <= len(raw), 'missing SIB/immediate')
        sib=raw[i];i+=1;idx=(sib>>3)&7;base=sib&7
        if idx!=4 or x:terms.append((GPR[idx+8*x],1<<(sib>>6)))
        if base==5 and mod==0:
            require(b==0, 'ignored REX.B outside no-base SIB profile')
            dispbytes=4
        else:terms.append((GPR[base+8*b],1))
    elif rm==5 and mod==0:
        require(x==b==0, 'ignored REX bits outside RIP-relative shuffle profile')
        dispbytes=4;terms.append(('RIP_NEXT',1))
    else:
        require(x==0, 'REX.X requires SIB')
        terms.append((GPR[rm+8*b],1))
    if mod==1:dispbytes=1
    if mod==2:dispbytes=4
    require(i+dispbytes+1 == len(raw), 'truncated displacement/immediate or trailing bytes')
    if dispbytes:disp=int.from_bytes(raw[i:i+dispbytes],'little',signed=True)
    if ('RIP_NEXT',1) in terms:
        terms.remove(('RIP_NEXT',1));disp+=site+len(raw)
    return Align(dst,None,raw[-1],(disp,tuple(terms)))


class ShuffleLifter(CopyLifter):
    def instruction(self, insn):
        if str(insn.getMnemonicString()).upper() != 'PALIGNR':
            return super().instruction(insn)
        raw=bytes(int(b)&255 for b in insn.getBytes())
        require(len(raw)==int(insn.getLength()), 'byte/length mismatch')
        e=decode(raw,int(insn.getAddress().getOffset()))
        self.validate_align(e,list(insn.getPcode()))
        src=(f'Extract 127 0 (Var R_YMM{e.src})' if e.src is not None else
             f'Load (Var V_MEM64) ({self.address_exp(e.address)}) LittleE 16')
        # One expression snapshots both sources before the single write. Keep
        # even zero-result memory operands syntactically present (fault boundary).
        pair=f'Concat (Extract 127 0 (Var R_YMM{e.dst})) ({src})'
        result=f'Extract 127 0 ({binary("RSHIFT",pair,word(e.immediate*8,256))})'
        return f'Move R_YMM{e.dst} (Concat (Extract 255 128 (Var R_YMM{e.dst})) ({result}))'

    def validate_align(self,e,ops):
        require(bool(ops), 'empty shuffle pcode')
        temps={};ranges=[];loads=0;final=None;used=set()
        addr=poly(*e.address) if e.address is not None else None
        old=('reg',e.dst,16)
        source=('reg',e.src,16) if e.src is not None else ('mem',addr,16)
        const=lambda n,w:('const',w,n)
        expected=('SUBPIECE',16,('INT_RIGHT',32,
                  ('INT_OR',32,('INT_LEFT',32,('INT_ZEXT',32,old),const(128,4)),
                   ('INT_ZEXT',32,source)),
                  ('INT_MULT',4,const(e.immediate,4),const(8,4))),const(0,4))
        size=lambda v:int(v.getSize())
        def read(v):
            nonlocal loads
            w=size(v);require(0<w<=32,'invalid/wide shuffle read')
            if v.isUnique():
                key=(int(v.getOffset()),w)
                require(key in temps,'uninitialized shuffle unique')
                value,deps=temps[key];used.update(deps);return value
            if v.isConstant():
                require(w in (4,8),'shuffle constant width')
                return const(int(v.getOffset()),w)
            if v.isAddress():
                require(str(v.getAddress().getAddressSpace().getName())=='ram' and e.src is None and w==16 and poly(int(v.getOffset()))==addr,'direct shuffle memory mismatch')
                loads+=1;return source
            require(v.isRegister(),'shuffle read space')
            if int(v.getOffset())>=0x1200:
                n,lo,w=self.vector_slice(v)
                require(lo==0 and w==16 and n in (e.dst,e.src),'shuffle vector source mismatch')
                return ('reg',n,16)
            name,bw,lo=self.register(v)
            require(name[2:] in GPR and w==8 and lo==0 and int(v.getOffset())==GPROFF[GPR.index(name[2:])],'shuffle address requires exact GPR64')
            return poly(0,((name[2:],1),))
        def address(value):
            if value[0]=='const' and value[1]==8:return poly(value[2])
            require(value[0]=='addr','nonaddress shuffle arithmetic');return value
        arity={'INT_ADD':2,'INT_MULT':2,'LOAD':2,'INT_ZEXT':1,'INT_LEFT':2,'INT_OR':2,'INT_RIGHT':2,'SUBPIECE':2}
        for index,op in enumerate(ops):
            code=str(op.getMnemonic());ins=list(op.getInputs());out=op.getOutput()
            require(code in arity and len(ins)==arity[code] and out is not None,'unmodeled/malformed shuffle raw pcode')
            used=set();w=size(out)
            if code=='LOAD':
                require(e.src is None and ins[0].isConstant() and size(ins[0])==4 and int(ins[0].getOffset())==433 and size(ins[1])==8 and w==16 and address(read(ins[1]))==addr,'shuffle load footprint/address')
                loads+=1;value=source
            elif code=='INT_ADD' or (code=='INT_MULT' and w==8):
                require(w==8 and all(size(v)==8 for v in ins),'shuffle address width')
                a,b=map(lambda v:address(read(v)),ins)
                if code=='INT_ADD':value=add(a,b)
                else:
                    require(not b[2],'shuffle address multiplier must be constant')
                    value=poly(a[1]*b[1],tuple((k,v*b[1]) for k,v in a[2]))
            else:
                widths={'INT_ZEXT':(32,[16]),'INT_LEFT':(32,[32,4]),'INT_OR':(32,[32,32]),'INT_MULT':(4,[4,4]),'INT_RIGHT':(32,[32,4]),'SUBPIECE':(16,[32,4])}
                require(code in widths and (w,[size(v) for v in ins])==widths[code],'shuffle DAG width mismatch')
                value=(code,w,*(read(v) for v in ins))
            if out.isUnique():
                key=(int(out.getOffset()),w);off=key[0]
                require(0<w<=32 and off>=0 and all(off>=a+b or a>=off+w for a,b in ranges),'shuffle unique overlap/reassignment')
                ranges.append(key);temps[key]=(value,used|{index})
            else:
                require(index==len(ops)-1 and final is None and out.isRegister(),'shuffle must have one final register write')
                n,lo,w=self.vector_slice(out)
                require((n,lo,w)==(e.dst,0,16),'shuffle destination width/offset')
                final=value
                require(used==set(range(index)),'dead/unconsumed shuffle DAG nodes')
        require(final==expected and loads==(1 if e.src is None else 0),'encoded/raw shuffle graph or memory footprint mismatch')
