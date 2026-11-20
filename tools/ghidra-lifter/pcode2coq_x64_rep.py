"""Opt-in REP MOVS/STOS profile over e25; exact encoding AND raw graph gate.

Only 64-bit addressing, canonical F3 [66|48] A4/A5/AA/AB encodings. The
pinned decoder represents the backedge as a machine self-BRANCH, not a relative
pcode branch. Fold precisely that prechecked loop into Picinae's bounded Rep.
Faults, interrupts/restarts, atomicity, timing and intermediate machine traces
are outside the sequential successful-completion projection (see unit notes).
"""
from pcode2coq_x64 import X64Lifter, Unsupported, seq

ENCODINGS = {
    bytes.fromhex(raw): (name+'.REP', kind, width)
    for kind, opcode, stem in [('movs',0xa4,'MOVS'),('stos',0xaa,'STOS')]
    for width, prefix, suffix in [(1,b'', 'B'),(2,b'\x66','W'),(4,b'','D'),(8,b'\x48','Q')]
    for raw, name in [( (b'\xf3'+prefix+bytes([opcode+(width!=1)])).hex(), stem+suffix)]
}


def expected_graph(kind, n, site, length):
    """Closed graph specification. Unique IDs are alpha-renamed, not trusted."""
    u = lambda i,w=8: ('u',i,w)
    r = lambda name,w=8: ('r','R_'+name,1 if name=='DF' else 64,0,w)
    c = lambda x,w=8: ('c',x,w)
    a = lambda x: ('a',x % (1<<64),8)
    mem = ('m',64,4)
    g = [('INT_EQUAL',u(0,1),[r('RCX'),c(0)]),
         ('CBRANCH',None,[a(site+length),u(0,1)]),
         ('INT_SUB',r('RCX'),[r('RCX'),c(1)])]
    def advance(reg, first):
        g.extend([('COPY',u(first),[r(reg)]),
                  ('INT_ADD',u(first+1),[r(reg),c(n)]),
                  ('INT_ZEXT',u(first+2),[r('DF',1)]),
                  ('INT_MULT',u(first+3),[c(2*n),u(first+2)]),
                  ('INT_SUB',r(reg),[u(first+1),u(first+3)])])
    advance('RDI',1)
    if kind=='movs':
        advance('RSI',5)
        g.extend([('LOAD',u(9,n),[mem,u(5)]),('COPY',u(10,n),[u(9,n)]),
                  ('STORE',None,[mem,u(1),u(10,n)])])
    else:
        g.extend([('COPY',u(5,n),[r('RAX',n)]),('STORE',None,[mem,u(1),u(5,n)])])
    g.append(('BRANCH',None,[a(site)]))
    return g


class X64RepLifter(X64Lifter):
    def instruction(self, insn):
        raw = bytes(int(b)&255 for b in insn.getBytes())
        mnemonic = str(insn.getMnemonicString()).upper()
        # e25 remains authoritative for scalar instructions. This never grants
        # scalar instructions extra prefix or internal-loop permissions.
        if raw not in ENCODINGS:
            return super().instruction(insn)
        name,kind,width = ENCODINGS[raw]
        if mnemonic != name or int(insn.getLength()) != len(raw):
            raise Unsupported('REP encoding/mnemonic/length mismatch')
        site = int(insn.getAddress().getOffset())
        if not 0 <= site < 1<<64:
            raise Unsupported('invalid REP address')
        ops = list(insn.getPcode())
        self.temps,self.ranges,self.initialized = {},[],set()
        def node(v, memory=False):
            if v is None: return None
            size,off = int(v.getSize()),int(v.getOffset())
            if memory:
                if not v.isConstant() or size!=4:
                    raise Unsupported('REP memory space varnode')
                space = self.lang.getAddressFactory().getAddressSpace(off)
                if space is None or str(space.getName())!='ram' or int(space.getSize())!=64:
                    raise Unsupported('REP nondefault memory space')
                return ('m',64,4)
            if v.isUnique():
                name = self.temp(v)
                return ('u',list(self.temps.values()).index(name),size)
            if v.isRegister():
                return ('r',*self.register(v),size)
            if v.isConstant(): return ('c',off,size)
            if v.isAddress() and str(v.getAddress().getAddressSpace().getName())=='ram':
                return ('a',off,size)
            raise Unsupported('REP unsupported varnode')
        graph=[]
        for op in ops:
            code,ins,out = self.shape(op)
            # Number outputs before inputs for deterministic alpha-normalization.
            output = node(out)
            graph.append((code,output,[node(v,code in ('LOAD','STORE') and i==0) for i,v in enumerate(ins)]))
        if graph != expected_graph(kind,width,site,len(raw)):
            raise Unsupported('REP raw loop graph differs from exact precheck/body/self-backedge template')
        # Emit existing scalar expressions in their original order. Snapshot the
        # entry RCX once as the Rep bound; zero performs no body operation, and
        # each validated body decrements RCX once. Maximum bound is 2^64-1.
        self.temps,self.ranges,self.initialized = {},[],set()
        body = seq([self.statement(op) for op in ops[2:-1]])
        return f'Rep (Var R_RCX) ({body})'
