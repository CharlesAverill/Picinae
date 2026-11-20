#!/usr/bin/env python3
"""Reproduce the bounded sample and complete copy-extent mnemonic inventory.
This operates on exact e01 objdump evidence; it is not a decoder or CFG audit.
"""
from pathlib import Path
import collections,json,re,sys
repo=Path(__file__).resolve().parents[2]
root=repo/'Examples/claude/inventory/e01-x86-inventory/generated'
notes=Path(__file__).resolve().parent
extents=[e for e in json.loads((root/'inventory.json').read_text())['extents'] if 'copy' in e['scope']]
selected={};counts=collections.Counter()
for line in (root/'disassembly.txt').read_text().splitlines():
    m=re.match(r'([0-9a-f]+)\s+([0-9a-f]+)\s+(\S+)(.*)',line)
    if not m:continue
    address,raw,opcode,operands=m.groups();address=int(address,16)
    owners=[e for e in extents if int(e['elf_address'],16)<=address<int(e['end_exclusive'],16)]
    if not owners:continue
    counts[opcode]+=1
    if opcode not in 'movdqu movdqa movups movaps movntdq vmovdqu vmovdqa vmovups vmovaps vmovntdq vzeroupper'.split():continue
    key=(opcode,'256' if 'ymm' in operands else '128','reg' if '[' not in operands else 'store' if 'PTR [' in operands.split(',')[0] else 'load',raw[:4] if raw.startswith(('c4','c5','44','45','66','f3')) else raw[:2])
    if key not in selected:selected[key]=dict(address=hex(address+0x100000),elf_address=hex(address),bytes=raw,assembly=opcode+operands,owners=owners[0]['names'])
for name,value in [('actual-selection.json',list(selected.values())),('copy-opcodes.json',dict(sorted(counts.items())))]:
    text=json.dumps(value,indent=2)+'\n'
    if sys.argv[1:]==['--update']:(notes/name).write_text(text)
    else:assert (notes/name).read_text()==text,name
print(f'PASS {len(extents)} copy extents, {len(selected)} selected instruction samples; EVEX negatives retained')
