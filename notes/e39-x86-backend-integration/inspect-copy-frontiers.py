"""Inspect actual pinned copy extents without granting new instruction support.
Counts are objdump evidence, not decoder reachability or whole-CFG claims.
"""
import collections,json,re
from pathlib import Path
repo=Path(__file__).resolve().parents[2];notes=Path(__file__).resolve().parent
source=repo/'Examples/claude/inventory/e01-x86-inventory/generated'
extents=[e for e in json.loads((source/'inventory.json').read_text())['extents'] if 'copy' in e['scope']]
groups={'lddqu':{'lddqu','vlddqu'},'df':{'cld','std'},'hints_fences':{'prefetchnta','prefetcht0','prefetcht1','sfence','lfence'},'shuffles':{'palignr','pshufb','vpalignr','vpshufb'},'evex':set(),'scalar_spellings_padding':{'jb','jae','inc','dec','nop','xchg','data16','cs','notrack'},'other_projection':{'vzeroall','xtest'}}
counts=collections.Counter();samples={k:[] for k in groups};evex=collections.Counter()
for line in (source/'disassembly.txt').read_text().splitlines():
    m=re.fullmatch(r'([0-9a-f]+)\s+([0-9a-f]+)\s+(\S+)(.*)',line)
    if not m:continue
    a,raw,op,operands=m.groups();a=int(a,16)
    owners=[e for e in extents if int(e['elf_address'],16)<=a<int(e['end_exclusive'],16)]
    if not owners:continue
    counts[op]+=1
    if raw.startswith('62'):evex[op]+=1
    for group,ops in groups.items():
        if op in ops or group=='evex' and raw.startswith('62'):
            if len(samples[group])<8:
                samples[group].append(dict(elf_address=hex(a),global_address=hex(a+0x100000),bytes=raw,assembly=op+operands,owners=owners[0]['names']))
old=json.loads((repo/'notes/e26-x86-sse-avx-lowering/copy-opcodes.json').read_text());assert dict(counts)==old
report=dict(copy_extents=len(extents),mnemonic_occurrences=dict(sorted(counts.items())),evex_occurrences=dict(sorted(evex.items())),examples=samples,actual_ghidra_first_rejection=dict(symbol='__memmove_avx_unaligned_erms',global_address='0x2a084b',mnemonic='JC',evidence='logs/03-old-negatives.log'))
(notes/'copy-frontiers.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS inspected',len(extents),'actual pinned copy extents; census matches accepted e26 evidence')
print('EVEX',dict(evex))
for group,ops in groups.items():print(group,{op:counts[op] for op in sorted(ops)})
print('Actual Ghidra JC is objdump jb; no alias lowering added. REP now composes, CLD/STD remain rejected.')
