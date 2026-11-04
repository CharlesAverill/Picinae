"""Opt-in SSE/AVX copy projection over canonical 256-bit YMM cells.

Decode the bounded encoding independently, then symbolically validate the entire
raw-pcode DAG and its footprint before emitting one architectural transfer.
Not an instruction-correctness theorem. Scalar and CET behavior stays in e25.
"""
from dataclasses import dataclass
from pcode2coq_x64 import X64Lifter, Unsupported
from pcode2coq_scalar import word, cast, binary, seq

MASK = (1 << 64)-1
GPR = 'RAX RCX RDX RBX RSP RBP RSI RDI R8 R9 R10 R11 R12 R13 R14 R15'.split()
GPROFF = [0,8,16,24,32,40,48,56,128,136,144,152,160,168,176,184]
MOVES = set('MOVDQU MOVDQA MOVUPS MOVAPS MOVNTDQ VMOVDQU VMOVDQA VMOVUPS VMOVAPS VMOVNTDQ VZEROUPPER'.split())


def require(ok, message):
    if not ok: raise Unsupported(message)


def poly(const=0, terms=()):
    d = {}
    for k,v in terms: d[k] = (d.get(k,0)+v)&MASK
    return ('addr', const&MASK, tuple(sorted((k,v) for k,v in d.items() if v)))


def add(a,b):
    require(a[0]==b[0]=='addr','nonaddress arithmetic')
    return poly(a[1]+b[1],a[2]+b[2])


@dataclass(frozen=True)
class Encoding:
    mnemonic: str
    width: int = 0                 # bytes
    vex: bool = False
    dst: int | None = None         # vector register, None means store
    src: int | None = None         # vector register, None means load
    address: tuple | None = None   # (displacement, ((GPR, scale), ...))


def decode(raw, site):
    require(1 <= len(raw) <= 15,'invalid encoding length')
    if raw == bytes.fromhex('c5f877'): return Encoding('VZEROUPPER',vex=True)
    i,pp,r,x,b,vex,width = 0,0,0,0,0,False,16
    if raw[0] in (0xc4,0xc5):
        vex=True
        if raw[0]==0xc5:
            require(len(raw)>=4,'truncated VEX2')
            v=raw[1];r=(~v>>7)&1;i=2
        else:
            require(len(raw)>=5,'truncated VEX3')
            v=raw[2];r=(~raw[1]>>7)&1;x=(~raw[1]>>6)&1;b=(~raw[1]>>5)&1;i=3
            require(raw[1]&31==1 and v&128==0,'only VEX 0F map, W=0')
        require(v&0x78==0x78,'reserved VEX.vvvv must be 1111')
        pp=v&3;width=32 if v&4 else 16
    else:
        if raw[i] in (0x66,0xf3): pp={0x66:1,0xf3:2}[raw[i]];i+=1
        if i<len(raw) and 0x40<=raw[i]<=0x4f:
            rex=raw[i];i+=1
            require(rex&8==0,'REX.W outside copy profile')
            r=(rex>>2)&1;x=(rex>>1)&1;b=rex&1
        require(i<len(raw) and raw[i]==0x0f,'not a legacy copy encoding/prefix');i+=1
    require(i+2<=len(raw),'missing opcode/ModRM')
    opcode,modrm=raw[i:i+2];i+=2
    table={(0x6f,2):('MOVDQU',False),(0x7f,2):('MOVDQU',True),
           (0x6f,1):('MOVDQA',False),(0x7f,1):('MOVDQA',True),
           (0x10,0):('MOVUPS',False),(0x11,0):('MOVUPS',True),
           (0x28,0):('MOVAPS',False),(0x29,0):('MOVAPS',True),
           (0xe7,1):('MOVNTDQ',True)}
    require((opcode,pp) in table,'unmodeled copy opcode/prefix')
    mnemonic,reverse=table[opcode,pp];mnemonic=('V' if vex else '')+mnemonic
    mod,reg,rm=modrm>>6,((modrm>>3)&7)+8*r,modrm&7
    if mod==3:
        require(opcode!=0xe7 and i==len(raw),'NT requires memory / trailing bytes')
        other=rm+8*b
        return Encoding(mnemonic,width,vex,other if reverse else reg,reg if reverse else other)
    terms=[];disp=0;dispbytes=0
    if rm==4:
        require(i<len(raw),'missing SIB')
        sib=raw[i];i+=1;idx=(sib>>3)&7;base=sib&7
        if idx!=4 or x: terms.append((GPR[idx+8*x],1<<(sib>>6)))
        if base==5 and mod==0: dispbytes=4
        else: terms.append((GPR[base+8*b],1))
    elif rm==5 and mod==0:
        dispbytes=4;terms.append(('RIP_NEXT',1))
    else: terms.append((GPR[rm+8*b],1))
    if mod==1:dispbytes=1
    if mod==2:dispbytes=4
    require(i+dispbytes==len(raw),'truncated displacement / trailing encoding bytes')
    if dispbytes: disp=int.from_bytes(raw[i:],'little',signed=True)
    if ('RIP_NEXT',1) in terms:
        terms.remove(('RIP_NEXT',1));disp+=site+len(raw)
    return Encoding(mnemonic,width,vex,None if reverse else reg,reg if reverse else None,(disp,tuple(terms)))


class CopyLifter(X64Lifter):
    """No generic vector read/write API: every vector instruction passes this gate."""
    def instruction(self, insn):
        name=str(insn.getMnemonicString()).upper()
        if name not in MOVES: return super().instruction(insn)
        raw=bytes(int(b)&255 for b in insn.getBytes())
        require(len(raw)==int(insn.getLength()),'byte/length mismatch')
        enc=decode(raw,int(insn.getAddress().getOffset()))
        require(name==enc.mnemonic,'mnemonic/encoding mismatch')
        self.validate_copy(enc,list(insn.getPcode()))
        if name=='VZEROUPPER':
            return seq([f'Move R_YMM{n} (Concat ({word(0,128)}) (Extract 127 0 (Var R_YMM{n})))' for n in range(16)])
        if enc.src is None:
            exp=f'Load (Var V_MEM64) ({self.address_exp(enc.address)}) LittleE {enc.width}'
        else:
            exp=f'Var R_YMM{enc.src}'
            if enc.width==16:exp=f'Extract 127 0 ({exp})'
        if enc.dst is None:
            return f'Move V_MEM64 (Store (Var V_MEM64) ({self.address_exp(enc.address)}) ({exp}) LittleE {enc.width})'
        if enc.width==16:
            exp=cast(exp,128,256) if enc.vex else f'Concat (Extract 255 128 (Var R_YMM{enc.dst})) ({exp})'
        return f'Move R_YMM{enc.dst} ({exp})'

    @staticmethod
    def address_exp(address):
        disp,terms=address;exps=[]
        for name,scale in terms:
            exp=f'Var R_{name}'
            if scale!=1:exp=binary('TIMES',exp,word(scale,64))
            exps.append(exp)
        if disp or not exps:exps.append(word(disp&MASK,64))
        result=exps[0]
        for exp in exps[1:]: result=binary('PLUS',result,exp)
        return result

    def vector_slice(self,v,allow_high=False):
        require(v.isRegister(),'expected vector register')
        off,size=int(v.getOffset()),int(v.getSize())
        n,lo=divmod(off-0x1200,64)
        require(0<=n<16 and size in (4,8,16,32,64) and lo+size<=64,'unmodeled vector slice')
        require(allow_high or lo+size<=32,'actual >256 vector read/write')
        reg=self.lang.getRegister(v.getAddress(),size)
        # Anonymous qwords occur only in the exact VZEROUPPER template.
        require(reg is not None,'anonymous vector slice')
        base=reg.getBaseRegister()
        require(str(base.getName())==f'ZMM{n}' and int(base.getBitLength())==512 and int(base.getAddress().getOffset())==0x1200+64*n,'wrong vector base metadata')
        return n,lo,size

    def validate_copy(self,e,ops):
        require(ops,'empty vector pcode')
        if e.mnemonic=='VZEROUPPER':
            # SLEIGH explicitly clears bits 128..511 of ZMM0..15. Check the
            # whole exact constant-zero template, project only bits 128..255.
            expected=[0x1200+64*n+lo for n in range(16) for lo in range(16,64,8)]
            require(len(ops)==len(expected),'VZEROUPPER zero template count')
            for op,offset in zip(ops,expected):
                ins=list(op.getInputs());out=op.getOutput()
                require(str(op.getMnemonic())=='COPY' and len(ins)==1 and out is not None and out.isRegister() and int(out.getOffset())==offset and int(out.getSize())==8 and ins[0].isConstant() and int(ins[0].getSize())==8 and int(ins[0].getOffset())==0,'VZEROUPPER zero template mismatch')
            return
        # Byte origins retain source snapshot and expose alias/partial-lane bugs.
        original={n:tuple(('reg',n,i) for i in range(64)) for n in range(16)}
        regs=original.copy();temps={};ranges=[];stores=[];loads=[];written=set();written_bytes=set()
        expected_addr=poly(*e.address) if e.address is not None else None
        expected_data=tuple(('mem',expected_addr,i) for i in range(e.width)) if e.src is None else original[e.src][:e.width]
        def width(v): return int(v.getSize())
        def read(v):
            size=width(v)
            require(0<size<=32,'actual >256 or zero-width data read')
            if v.isUnique():
                key=(int(v.getOffset()),size)
                require(key in temps,'uninitialized unique read');return temps[key]
            if v.isConstant():
                require(size<=8,'wide constants outside profile')
                return poly(int(v.getOffset()))
            if v.isAddress() and str(v.getAddress().getAddressSpace().getName())=='ram':
                require(e.src is None and size==e.width and poly(int(v.getOffset()))==expected_addr and not stores,'direct memory read mismatch')
                loads.append(expected_addr);return expected_data
            require(v.isRegister(),'unmodeled vector pcode input space')
            off=int(v.getOffset())
            if off>=0x1200:
                n,lo,size=self.vector_slice(v);return regs[n][lo:lo+size]
            name,bw,lo=self.register(v)
            require(name[2:] in GPR and size==8 and lo==0 and off==GPROFF[GPR.index(name[2:])],'non-GPR64 address input')
            return poly(0,((name[2:],1),))
        def write(v,value,zero_extension=False):
            size=width(v)
            if v.isUnique():
                require(0<size<=32 and int(v.getOffset())>=0,'wide/invalid unique write')
                off=int(v.getOffset());key=(off,size)
                require(all(key==k or off>=k[0]+k[1] or k[0]>=off+size for k in ranges),'overlapping unique slices')
                if key not in ranges:ranges.append(key)
                temps[key]=value;return
            if v.isAddress() and str(v.getAddress().getAddressSpace().getName())=='ram':
                require(e.dst is None and size==e.width and poly(int(v.getOffset()))==expected_addr and value==expected_data,'direct memory write mismatch')
                stores.append(expected_addr);return
            require(v.isRegister(),'unmodeled vector output space')
            n,lo,size=self.vector_slice(v,allow_high=zero_extension)
            require(n==e.dst and lo+size<= (64 if zero_extension else e.width),'write outside encoded destination')
            require(isinstance(value,tuple) and len(value)==size,'vector write width/type mismatch')
            regs[n]=regs[n][:lo]+value+regs[n][lo+size:];written.add(n);written_bytes.update(range(lo,lo+size))
        arities={'COPY':1,'LOAD':2,'STORE':3,'INT_ADD':2,'INT_MULT':2,'SUBPIECE':2,'INT_ZEXT':1,'CALLOTHER':2}
        for op in ops:
            code=str(op.getMnemonic());ins=list(op.getInputs());out=op.getOutput()
            require(code in arities and len(ins)==arities[code] and (out is None)==(code=='STORE'),'unsupported/malformed vector raw pcode')
            if code in ('LOAD','STORE'):
                space=ins[0]
                require(space.isConstant() and int(space.getOffset())==433 and width(space)==4,'wrong raw memory space ID')
                address=read(ins[1]);require(width(ins[1])==8 and address==expected_addr,'encoded/raw effective address mismatch')
                if code=='LOAD':
                    require(e.src is None and width(out)==e.width and not stores,'unexpected/wrong-width load')
                    loads.append(address);write(out,expected_data)
                else:
                    require(e.dst is None and width(ins[2])==e.width and read(ins[2])==expected_data,'encoded/raw store data mismatch')
                    stores.append(address)
            elif code in ('INT_ADD','INT_MULT'):
                require(out.isUnique() and width(out)==8 and all(width(v)==8 for v in ins),'nonaddress arithmetic output')
                a,b=map(read,ins)
                if code=='INT_ADD':value=add(a,b)
                else:
                    require(a[0]==b[0]=='addr' and not b[2],'nonconstant address multiplier')
                    value=poly(a[1]*b[1],tuple((k,v*b[1]) for k,v in a[2]))
                write(out,value)
            elif code=='INT_ZEXT':
                # The only accepted >256 varnode is SLEIGH's zero-extension
                # OUTPUT for an encoded VEX <=256 transfer. No wide data read.
                require(e.vex and e.dst is not None and out.isRegister() and width(out)==64 and width(ins[0])==e.width,'invalid projected zero-extension')
                value=read(ins[0]);require(len(value)==e.width,'extension type mismatch')
                write(out,value+(0,)*(64-e.width),True)
            elif code=='CALLOTHER':
                # Pinned avx.sinc uses vmovntdq_avx (userop 303). Its only
                # observation here is the sequential value passed to STORE.
                require(e.mnemonic=='VMOVNTDQ' and ins[0].isConstant() and int(ins[0].getOffset())==303 and width(ins[0])==4 and out.isUnique() and width(out)==e.width and width(ins[1])==e.width,'unmodeled vector userop')
                write(out,read(ins[1]))
            else:
                value=read(ins[0])
                if code=='SUBPIECE':
                    require(ins[1].isConstant() and width(ins[1])==4,'nonconstant lane offset')
                    lo=int(ins[1].getOffset());require(value[0]!='addr' and 0<=lo and lo+width(out)<=len(value),'invalid lane extraction')
                    value=value[lo:lo+width(out)]
                else:require(width(out)==width(ins[0]),'COPY width mismatch')
                write(out,value)
        if e.dst is None:
            require(len(stores)==1 and not loads and not written,'store footprint mismatch')
        else:
            expected=expected_data+((0,)*(64-e.width) if e.vex else original[e.dst][e.width:])
            require(regs[e.dst]==expected and written=={e.dst} and written_bytes==set(range(64 if e.vex else e.width)) and not stores,'encoded/raw register effect mismatch')
            # VMOVAPS256 SLEIGH has a duplicate same-address read. Only this
            # known shape may repeat; no additional memory observations pass.
            count=2 if e.mnemonic=='VMOVAPS' and e.width==32 and e.src is None else 1
            require(len(loads)==(count if e.src is None else 0),'load footprint mismatch')
