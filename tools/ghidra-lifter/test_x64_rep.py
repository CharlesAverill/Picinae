#!/usr/bin/env python3
"""REP raw-pcode/IL/independent scalar-memory oracle tests; engineering only.
Parser/evaluator adapted from test_scalar with Rep and modular byte addressing.
"""
import copy
import json
import re
import random
import unittest
from pathlib import Path
from test_x64 import Language, instruction, state, node, Insn
from pcode2coq_x64 import X64Lifter, Unsupported
from pcode2coq_x64_rep import X64RepLifter, ENCODINGS
from test_scalar import signed

REPO=Path(__file__).resolve().parents[2]
ART=REPO/'Examples/claude/lifter'
MASK=(1<<64)-1

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
        if token == 'Rep': return ('rep', exp(), stmt())
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
        return sum(mem.get((address+i) % (1<<64), 0) << (8*i) for i in range(n)), 8*n
    if op == 'store':
        m, a, d, n = args; mem, _ = evaluate(m, state); address, _ = evaluate(a, state); data, _ = evaluate(d, state)
        result = mem.copy(); result.update({(address+i) % (1<<64): (data >> (8*i)) & 255 for i in range(n)})
        return result, 'memory'
    raise AssertionError(op)


def execute(tree, state):
    op, *args = tree
    if op == 'seq':
        for s in args[0]:
            jump = execute(s, state)
            if jump is not None: return jump
    elif op == 'rep':
        count = evaluate(args[0], state)[0]
        if count > 10000: raise AssertionError('test execution budget')
        for _ in range(count):
            jump = execute(args[1], state)
            if jump is not None: return jump
    elif op == 'move': state[args[0]] = evaluate(args[1], state)
    elif op == 'if': return execute(args[1] if evaluate(args[0], state)[0] else args[2], state)
    elif op == 'jump': return evaluate(args[0], state)[0]
    elif op != 'nop': raise AssertionError(op)


def raw_run(row, s):
    """Execute the captured raw pcode, including actual precheck/self-backedge.
    Separate register bank, memory, and unique storage. No use of the emitter.
    """
    regs={k[2:]:v[0] for k,v in s.items() if k.startswith('R_')}
    mem=s['V_MEM64'][0].copy(); unique={}; ops=row['ops']; pc=0; steps=0
    def read(v):
        if v['space']=='const': return v['offset'] % (1<<(8*v['size']))
        if v['space']=='unique':return unique[v['offset'],v['size']]
        if v['space']=='register':
            shift=(v['offset']-v['base_offset'])*8
            return (regs[v['base']]>>shift) % (1<<(8*v['size']))
        return v['offset']
    def write(v,x):
        x %= 1<<(8*v['size'])
        if v['space']=='unique':unique[v['offset'],v['size']]=x
        else:regs[v['base']]=x
    while pc<len(ops):
        steps+=1
        assert steps<10000
        o=ops[pc];code=o['code'];vs=o['inputs'];a=[read(v) for v in vs]
        if code=='CBRANCH':
            if a[1]:assert a[0]==int(row['address'],16)+len(bytes.fromhex(row['bytes']));break
        elif code=='BRANCH':
            assert a[0]==int(row['address'],16);pc=0;continue
        elif code=='LOAD':write(o['output'],sum(mem.get((a[1]+i)&MASK,0)<<(8*i) for i in range(o['output']['size'])))
        elif code=='STORE':mem.update({(a[1]+i)&MASK:(a[2]>>(8*i))&255 for i in range(vs[2]['size'])})
        else:
            result={'COPY':lambda:a[0],'INT_ZEXT':lambda:a[0], 'INT_EQUAL':lambda:int(a[0]==a[1]),
                    'INT_SUB':lambda:a[0]-a[1], 'INT_ADD':lambda:a[0]+a[1], 'INT_MULT':lambda:a[0]*a[1]}[code]()
            write(o['output'],result)
        pc+=1
    return regs,mem


def oracle(s,kind,width):
    regs={k[2:]:v[0] for k,v in s.items() if k.startswith('R_')}
    mem=s['V_MEM64'][0].copy();count=regs['RCX'];step=width if regs['DF']==0 else -width
    # Read the entire element before its store. Subsequent iterations see writes.
    for _ in range(count):
        data=[mem.get((regs['RSI']+i)&MASK,0) for i in range(width)] if kind=='movs' else [(regs['RAX']>>(8*i))&255 for i in range(width)]
        mem.update({(regs['RDI']+i)&MASK:b for i,b in enumerate(data)})
        regs['RDI']=(regs['RDI']+step)&MASK
        if kind=='movs':regs['RSI']=(regs['RSI']+step)&MASK
        regs['RCX']-=1
    return regs,mem


class Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows=[]
        for d in ('x64_rep_pinned','x64_rep_synthetic'):
            cls.rows.extend(json.loads((ART/d/'e27_rep_amd64.pcode.json').read_text()))
        cls.lang=Language(cls.rows)
    def test_actual_graph_reemission_and_e25_rejection(self):
        for row in self.rows:
            text=X64RepLifter(self.lang).instruction(instruction(row))
            self.assertTrue(text.startswith('Rep (Var R_RCX)'))
            self.assertNotIn('Jmp',text)
            for d in ('x64_rep_pinned','x64_rep_synthetic'):
                p=ART/d/'e27_rep_amd64.v'
                if f"| {row['address']} =>" in p.read_text():self.assertIn('\t'+text+'\n)',p.read_text())
            with self.assertRaises(Unsupported):X64Lifter(self.lang).instruction(instruction(row))
    def test_all_sites_counts_directions_widths_wrap_and_alias(self):
        rng=random.Random(27);cases=0
        for row in self.rows:
            _,kind,width=ENCODINGS[bytes.fromhex(row['bytes'])]
            tree=parse(X64RepLifter(self.lang).instruction(instruction(row)))
            for count in (0,1,2,3,9):
                for df in (0,1):
                    # Disjoint, identity, byte-overlap both directions, element
                    # overlap, high addresses and crossing modular byte boundary.
                    for src,dst in [(0x100,0x200),(0x100,0x100),(0x100,0x101),(0x101,0x100),
                                    (0x100,0x100+width),(MASK-2,1),(1,MASK-2),(MASK-2,MASK-1)]:
                        s=state()
                        for k,(x,w) in list(s.items()):
                            if k!='V_MEM64':s[k]=(rng.getrandbits(w),w)
                        s.update(R_RCX=(count,64),R_DF=(df,1),R_RSI=(src,64),R_RDI=(dst,64))
                        mem={a&rMASK:rng.randrange(256) for rMASK in [MASK] for a in list(range(-100,101))+list(range(0x80,0x280))}
                        s['V_MEM64']=(mem,'memory')
                        expected=oracle(s,kind,width)
                        self.assertEqual(raw_run(row,s),expected)
                        execute(tree,s)
                        actual=({k[2:]:v[0] for k,v in s.items() if k.startswith('R_')},s['V_MEM64'][0])
                        self.assertEqual(actual,expected,(row['assembly'],count,df,src,dst))
                        cases+=1
        print('PASS',cases,'raw/IL/oracle cases (all architectural registers, flags, full byte memory)')
    def test_zero_performs_no_memory_access(self):
        class NoAccess(dict):
            def get(self,*args):raise AssertionError('zero-count load')
            def copy(self):raise AssertionError('zero-count store')
        for row in self.rows:
            s=state();s['V_MEM64']=(NoAccess(),'memory')
            execute(parse(X64RepLifter(self.lang).instruction(instruction(row))),s)
            self.assertEqual(s['R_RCX'],(0,64))
    def test_large_count_bound_is_not_truncated(self):
        row=self.rows[0];tree=parse(X64RepLifter(self.lang).instruction(instruction(row)))
        s=state();s['R_RCX']=(MASK,64)
        self.assertEqual(tree[1][0][0],'rep')
        self.assertEqual(evaluate(tree[1][0][1],s),(MASK,64))
    def test_mutated_loop_graphs_reject(self):
        checked=0
        for row in self.rows:
            variants=[]
            for i,o in enumerate(row['ops']):
                bad=copy.deepcopy(row);bad['ops'][i]['code']='COPY' if o['code']!='COPY' else 'INT_NEGATE';variants.append(bad)
                bad=copy.deepcopy(row);del bad['ops'][i];variants.append(bad)
                for key,j,v in [('output',None,o['output'])]+[('inputs',j,v) for j,v in enumerate(o['inputs'])]:
                    if v is None:continue
                    for field in ('offset','size'):
                        bad=copy.deepcopy(row);b=bad['ops'][i][key] if j is None else bad['ops'][i][key][j]
                        b[field]+=1;variants.append(bad)
            bad=copy.deepcopy(row);bad['ops'].append(copy.deepcopy(row['ops'][0]));variants.append(bad)
            bad=copy.deepcopy(row);bad['ops'][-1]['inputs'][0]['space']='const';bad['ops'][-1]['inputs'][0]['offset']=(1<<64)-(len(row['ops'])-1);variants.append(bad)
            bad=copy.deepcopy(row);bad['ops'][0],bad['ops'][2]=bad['ops'][2],bad['ops'][0];variants.append(bad)
            for bad in variants:
                # Build the language from ORIGINAL rows, so corrupt register
                # offsets cannot redefine the architectural register bank.
                with self.assertRaises(Unsupported):X64RepLifter(self.lang).instruction(instruction(bad))
                checked+=1
        print('PASS',checked,'graph mutations rejected')
    def test_prefix_encoding_mnemonic_loop_variants_reject(self):
        row=self.rows[0];i=instruction(row)
        for raw in ('67f3a4','64f3a4','f2a4','f3f3a4','f36666a5','66f3a5','f340a4','f349a5','f3a6','f2ae','f0f3aa','a4'):
            bad=copy.deepcopy(i);bad.raw=bytes.fromhex(raw)
            with self.assertRaises(Unsupported):X64RepLifter(self.lang).instruction(bad)
        bad=copy.deepcopy(i);bad.mnemonic='CMPSB.REPE'
        with self.assertRaises(Unsupported):X64RepLifter(self.lang).instruction(bad)
    def test_alpha_renaming_is_allowed_only_without_overlap(self):
        row=self.rows[0];bad=copy.deepcopy(row)
        for o in bad['ops']:
            for v in o['inputs']+[o['output']]:
                if v and v['space']=='unique':v['offset']+=0x100000
        self.assertEqual(X64RepLifter(self.lang).instruction(instruction(bad)),X64RepLifter(self.lang).instruction(instruction(row)))

if __name__=='__main__':unittest.main(verbosity=2)
