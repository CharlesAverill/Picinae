#!/usr/bin/env python3
"""Deterministic, nonexecuting ELF/debug/source inventory for the pinned libc."""
import argparse
import bisect
from collections import defaultdict
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import struct
import subprocess

from retrieve import BUILD_ID, DEFAULT_ROOT, LIBC_SHA, VERSION, fields, sha

BASE = 0x100000
COPY = ('memcpy', 'memmove', 'mempcpy')
STRINGS = ('memset', 'memcmp', 'strlen', 'strcpy', 'strcmp', 'memchr', 'strnlen',
           'strncmp', 'strncpy', 'stpcpy', 'strcat')
EXTRA = ('bcmp', 'bcopy', 'bzero', 'memcmpeq', 'memccpy', 'memrchr', 'rawmemchr',
         'strchr', 'strchrnul', 'strrchr', 'strspn', 'strcspn', 'strpbrk',
         'stpncpy', 'strncat', 'strstr', 'strcasestr', 'memmem')
FAMILIES = COPY + STRINGS + EXTRA
PATTERN = re.compile(r'^(?:__GI_)?_*(' + '|'.join(sorted(FAMILIES, key=len, reverse=True)) + r')(?=_|@|$)')
REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def command(*args):
    return subprocess.check_output(list(map(str, args)), text=True, stderr=subprocess.PIPE,
                                   env={**os.environ, 'LC_ALL': 'C'})


def write_json(out, name, value):
    (out / name).write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


class ELF:
    def __init__(self, path):
        self.data = path.read_bytes()
        assert self.data[:6] == b'\x7fELF\x02\x01', 'ELF64 little-endian required'
        e = struct.unpack_from('<HHIQQQIHHHHHH', self.data, 16)
        assert e[0:2] == (3, 62), 'ET_DYN x86_64 required'
        self.loads = []
        for i in range(e[9]):
            p = struct.unpack_from('<IIQQQQQQ', self.data, e[4] + i * e[8])
            if p[0] == 1:
                self.loads.append(dict(flags=p[1], offset=p[2], vaddr=p[3], filesz=p[5], memsz=p[6]))

    def offset(self, address, size):
        for p in self.loads:
            if p['vaddr'] <= address and address + size <= p['vaddr'] + p['filesz']:
                return p['offset'] + address - p['vaddr']
        raise ValueError(f'not file backed: {address:#x}+{size}')

    def read(self, address, size):
        off = self.offset(address, size)
        return self.data[off:off + size]

    def initial(self, address, size):
        for p in self.loads:
            if p['vaddr'] <= address and address + size <= p['vaddr'] + p['memsz']:
                file_size = max(0, min(size, p['vaddr'] + p['filesz'] - address))
                return (self.read(address, file_size) if file_size else b'') + bytes(size - file_size)
        raise ValueError(f'not mapped: {address:#x}+{size}')


def symbols(path, origin):
    result = []
    text = command('readelf', '-Ws', path)
    for line in text.splitlines():
        m = re.match(r'\s*\d+:\s+([0-9a-f]+)\s+(\d+)\s+(\w+)\s+(\w+)\s+(\w+)\s+(\w+)\s+(\S+)', line)
        if not m:
            continue
        address, size, typ, bind, vis, section, name = m.groups()
        if section not in ('UND', 'ABS') and int(address, 16) and typ in ('FUNC', 'IFUNC', 'OBJECT'):
            result.append(dict(name=name, address=int(address, 16), size=int(size), type=typ,
                               binding=bind, visibility=vis, table=origin))
    return result


def disassemble(libc, elf):
    # Wide instruction column prevents continuation lines. No target code is run.
    text = command('objdump', '-d', '-w', '--insn-width=16', '-M', 'intel', libc)
    result = {}
    for line in text.splitlines():
        m = re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(\S.*)', line)
        if m:
            addr = int(m[1], 16)
            data = bytes.fromhex(m[2])
            assert elf.read(addr, len(data)) == data
            result[addr] = dict(address=addr, length=len(data), bytes=data.hex(), asm=m[3].strip())
    return result


def impl_list(source):
    """Parse macro calls, preserving CPU-feature expressions, without executing C."""
    text = (source / 'sysdeps/x86_64/multiarch/ifunc-impl-list.c').read_text()
    rows = []
    for match in re.finditer(r'\bIFUNC_IMPL_ADD\s*\(', text):
        start = match.end()
        depth, end = 1, start
        while depth:
            if text[end] == '(':
                depth += 1
            elif text[end] == ')':
                depth -= 1
            end += 1
        args, last, depth = [], start, 0
        for pos in range(start, end - 1):
            char = text[pos]
            depth += (char == '(') - (char == ')')
            if char == ',' and not depth:
                args.append(text[last:pos]); last = pos + 1
        args.append(text[last:end - 1])
        args = [' '.join(a.split()) for a in args]
        if len(args) == 5 and PATTERN.match(args[2]):
            rows.append(dict(public=args[2], condition=args[3], implementation=args[4],
                             source_line=text.count('\n', 0, match.start()) + 1))
    return rows


def normalize_mnemonic(asm):
    asm = asm.replace('MOVSB.REP', 'REP MOVSB')
    words = asm.upper().replace('REP.', 'REP ').replace('REPE.', 'REPE ').split()
    while words[0] in ('CS', 'DS', 'ES', 'DATA16', 'ADDR32'):
        words.pop(0)
    aliases = {'JC':'JB', 'JNC':'JAE', 'JZ':'JE', 'JNZ':'JNE', 'JNA':'JBE', 'JNBE':'JA',
               'JNG':'JLE', 'JNLE':'JG', 'JNGE':'JL', 'JNL':'JGE', 'MOVSQ':'MOVS', 'MOVSD':'MOVS',
               'MOVSW':'MOVS', 'MOVSB':'MOVS', 'RETQ':'RET', 'RETN':'RET', 'SAL':'SHL'}
    return ' '.join(aliases.get(w, w) for w in words[:2]) if words[0] in ('REP', 'REPE', 'REPNE') else aliases.get(words[0], words[0])


def compare_lift(path, elf, insns, by_address):
    text = path.read_text()
    matches = list(re.finditer(r'\(\* 0x([0-9a-fA-F]+): ([^\n]+) \*\)\s*\(\*[^\n]*\*\)\s*\| (0x[0-9a-fA-F]+) => Some \((\d+),', text))
    assert matches, path
    rows, issues = [], []
    for m in matches:
        ghidra, annotation, il, length = int(m[1], 16), m[2], int(m[3], 16), int(m[4])
        address = ghidra - BASE
        expected_il = ghidra if path.name == 'memcpy_amd64.v' else address - 0x1a0840
        assert il == expected_il, (path, hex(ghidra), hex(il))
        actual = insns.get(address)
        row = dict(elf_address=hex(address), ghidra_address=hex(ghidra), il_address=hex(il),
                   il_length=length, annotation=annotation, bytes=elf.read(address, length).hex(),
                   disassembly=actual['asm'] if actual else None,
                   boundary_and_length_match=bool(actual and actual['length'] == length),
                   mnemonic_match=bool(actual and normalize_mnemonic(annotation) == normalize_mnemonic(actual['asm'])))
        if not row['boundary_and_length_match'] or not row['mnemonic_match']:
            issues.append(row)
        rows.append(row)
    addresses = {int(r['elf_address'], 16) for r in rows}
    ranges = []
    for r in sorted(rows, key=lambda r: int(r['elf_address'], 16)):
        start = int(r['elf_address'], 16)
        end = start + r['il_length']
        if ranges and ranges[-1][1] == start:
            ranges[-1][1] = end
        else:
            ranges.append([start, end])
    missing_targets = []
    for addr in sorted(addresses):
        actual = insns[addr]
        m = re.match(r'(j\w+|call)\s+([0-9a-f]+)\b', actual['asm'])
        if m and int(m[2], 16) not in addresses:
            missing_targets.append(dict(site=hex(addr), target=hex(int(m[2], 16)), instruction=actual['asm']))
    return dict(file=str(path.relative_to(REPO)), sha256=sha(path), instructions=len(rows),
                matched_boundaries=sum(r['boundary_and_length_match'] for r in rows),
                matched_mnemonics=sum(r['mnemonic_match'] for r in rows), issues=issues,
                ranges=[dict(start=hex(a), end_exclusive=hex(b), size=b-a,
                             sha256=hashlib.sha256(elf.read(a, b-a)).hexdigest(),
                             symbols_at_start=sorted(by_address.get(a, []))) for a,b in ranges],
                direct_targets_outside_lift=missing_targets, instruction_evidence=rows,
                il_address_mapping_verified=True,
                limitation='Instruction boundaries/lengths, IL code address mapping and normalized mnemonics are checked against exact bytes; IL semantics and original lifter reproducibility are not certified.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    ap.add_argument('--output', type=Path, default=HERE / 'generated')
    args = ap.parse_args()
    root, out = args.root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    libc = root / 'runtime/lib/x86_64-linux-gnu/libc.so.6'
    debug = root / f'debug/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug'
    source = root / 'source'
    assert sha(libc) == LIBC_SHA
    provenance = {}
    for name in ('Packages', 'Sources'):
        records = [fields(p) for p in lzma.decompress((root/'downloads'/f'{name}.xz').read_bytes()).decode().split('\n\n')]
        provenance[name] = [r for r in records if r.get('Version') == VERSION and r.get('Package') in ('glibc','libc6','libc6-dbg')]
    write_json(out, 'package-provenance.json', provenance)
    for path in (libc, debug):
        assert re.search(r'Build ID: (\w+)', command('readelf', '-n', path))[1] == BUILD_ID
    elf = ELF(libc)
    all_symbols = symbols(libc, 'dynsym') + symbols(debug, 'debug-symtab')
    by_address = defaultdict(set)
    for s in all_symbols:
        if s['type'] in ('FUNC', 'IFUNC'):
            by_address[s['address']].add(s['name'])
    selected = []
    for s in all_symbols:
        m = PATTERN.match(s['name'])
        if m and s['type'] in ('FUNC', 'IFUNC'):
            selected.append({**s, 'family': m[1], 'scope': 'copy' if m[1] in COPY else 'strings' if m[1] in STRINGS else 'extra'})
    selected.sort(key=lambda s: (s['address'], s['size'], s['name'], s['table']))
    insns = disassemble(libc, elf)
    ordered = sorted(insns)
    groups = defaultdict(list)
    for s in selected:
        groups[(s['address'], s['size'])].append(s)
    bodies = []
    for (start, size), syms in sorted(groups.items()):
        assert size > 0
        end = start + size
        names = sorted({s['name'] for s in syms})
        body_insns = [insns[a] for a in ordered[bisect.bisect_left(ordered, start):bisect.bisect_left(ordered, end)]]
        assert body_insns and body_insns[0]['address'] == start
        # Some symbol extents end before alignment padding, which remains executable fallthrough.
        edges, data_refs, indirect = [], [], []
        for i in body_insns:
            m = re.match(r'(j\w+|call)\s+([0-9a-f]+)\b', i['asm'])
            if m:
                target = int(m[2], 16)
                if not start <= target < end:
                    edges.append(dict(site=hex(i['address']), kind=m[1], target=hex(target),
                                      symbols_at_target=sorted(by_address.get(target, []))))
            elif re.match(r'(jmp|call)\s', i['asm']):
                indirect.append(dict(site=hex(i['address']), instruction=i['asm']))
            m = re.search(r'#\s*([0-9a-f]+)\b', i['asm'])
            if m:
                target = int(m[1], 16)
                data_refs.append(dict(site=hex(i['address']), target=hex(target), symbols_at_target=sorted(
                    {s['name'] for s in all_symbols if s['address'] == target})))
        last = body_insns[-1]
        if not re.match(r'(ret|jmp|ud2|hlt)\b', last['asm']):
            target = last['address'] + last['length']
            edges.append(dict(site=hex(last['address']), kind='fallthrough', target=hex(target),
                              symbols_at_target=sorted(by_address.get(target, []))))
        contained = sorted({s['name'] for s in all_symbols if s['type'] in ('FUNC','IFUNC') and start < s['address'] < end})
        bodies.append(dict(elf_address=hex(start), ghidra_address=hex(start + BASE), end_exclusive=hex(end),
                           file_offset=hex(elf.offset(start, size)), size=size, sha256=hashlib.sha256(elf.read(start, size)).hexdigest(),
                           names=names, all_names_at_entry=sorted(by_address[start]), contained_entries=contained,
                           direct_external_edges=edges, rip_references=data_refs, indirect_transfers=indirect,
                           first_bytes=elf.read(start, min(size, 16)).hex(),
                           scope=sorted({s['scope'] for s in syms})))
    for body in bodies:
        body['identical_byte_extents'] = [b['elf_address'] for b in bodies
            if b is not body and b['size'] == body['size'] and b['sha256'] == body['sha256']]
        for edge in body['direct_external_edges']:
            address = int(edge['target'], 16)
            # Resolve alignment-only fallthrough bridges, without treating them as a full CFG.
            cursor = address
            if edge['kind'] == 'fallthrough':
                while cursor in insns and (re.search(r'\bnop\b', insns[cursor]['asm']) or insns[cursor]['asm'] == 'xchg   ax,ax'):
                    cursor += insns[cursor]['length']
                edge['after_alignment'] = hex(cursor)
            edge['target_extent_owners'] = [b['names'] for b in bodies
                if int(b['elf_address'],16) <= cursor < int(b['end_exclusive'],16)]
    for s in selected:
        s['elf_address'] = hex(s.pop('address'))
        s['ghidra_address'] = hex(int(s['elf_address'],16) + BASE)
        s['version'] = s['name'].split('@', 1)[1].lstrip('@') if '@' in s['name'] else None
    write_json(out, 'inventory.json', dict(version=VERSION, libc_sha256=LIBC_SHA, build_id=BUILD_ID,
        elf_type='ET_DYN', machine='EM_X86_64', ghidra_base=hex(BASE), load_segments=elf.loads,
        scope=dict(copy=list(COPY), strings=list(STRINGS), extra=list(EXTRA)), symbols=selected, extents=bodies,
        extent_policy='Exact st_value/st_size, half-open, hashed in the runtime ELF; an extent is not necessarily a complete reachable implementation. External edges and shared-body entries require composition. Padding fallthrough and indirect transfers are not resolved into a complete CFG.'))
    # Source list cross-check makes the candidate inventory fail closed on omitted/missing implementations.
    declared = impl_list(source)
    observed = {s['name'].split('@')[0] for s in selected}
    for row in declared:
        row['present_in_debug_symbols'] = row['implementation'] in observed
    assert declared and all(r['present_in_debug_symbols'] for r in declared)
    write_json(out, 'ifunc-implementations.json', declared)
    resolvers = []
    for b in bodies:
        syms = groups[(int(b['elf_address'],16),b['size'])]
        if not any(s['type']=='IFUNC' for s in syms):
            continue
        resolvers.append(dict(elf_address=b['elf_address'], names=b['names'],
                              rip_references=b['rip_references'], sha256=b['sha256']))
    write_json(out,'resolvers.json',resolvers)
    data = []
    for s in sorted(all_symbols, key=lambda s: (s['address'], s['name'])):
        if s['type'] == 'OBJECT' and s['name'].startswith('__x86_'):
            raw = elf.initial(s['address'], s['size'])
            data.append(dict(**s, ghidra_address=hex(s['address'] + BASE), initial_bytes=raw.hex(),
                             initial_unsigned_value=int.from_bytes(raw, 'little'), sha256=hashlib.sha256(raw).hexdigest()))
    write_json(out, 'dispatch-data.json', data)
    # Disassembly includes entry stubs, shared regions, IFUNC selectors and the implementation-list routine.
    dump = []
    for body in bodies:
        start, end = int(body['elf_address'],16), int(body['end_exclusive'],16)
        dump += ['\n# ' + ' | '.join(body['names']), f'# ELF {start:#x} Ghidra {start+BASE:#x} size {end-start} SHA256 {body["sha256"]}']
        for a in ordered[bisect.bisect_left(ordered, start):bisect.bisect_left(ordered, end)]:
            i = insns[a]
            dump.append(f'{a:08x}  {i["bytes"]:32s}  {i["asm"]}')
    impl = next(s for s in all_symbols if s['name'].split('@')[0] == '__libc_ifunc_impl_list')
    dump.append('\n# __libc_ifunc_impl_list (diagnostic enumerator, not the runtime selector)')
    for a in ordered[bisect.bisect_left(ordered,impl['address']):bisect.bisect_left(ordered,impl['address']+impl['size'])]:
        i=insns[a]; dump.append(f'{a:08x}  {i["bytes"]:32s}  {i["asm"]}')
    (out / 'disassembly.txt').write_text('\n'.join(dump) + '\n')
    (out / 'symbols.tsv').write_text('scope\tfamily\tsymbol\tversion\ttype\tbinding\ttable\telf\tghidra\tsize\n' + ''.join(
        '\t'.join(str(s.get(k) or '-') for k in ['scope','family','name','version','type','binding','table','elf_address','ghidra_address','size'])+'\n' for s in selected))
    units = []
    for b in bodies:
        names=b['names']
        eligible=[n for n in names if not n.startswith('__GI_') and not n.endswith('_ifunc') and '@' not in n]
        eligible=eligible or [n for n in names if not n.startswith('__GI_') and not n.endswith('_ifunc')]
        canonical=next((n for n in eligible if n.startswith('__memmove_')),eligible[0])
        if any(s['type']=='IFUNC' for s in groups[(int(b['elf_address'],16),b['size'])]):
            kind='resolver'
            canonical=min((s['name'] for s in groups[(int(b['elf_address'],16),b['size'])]
                if s['type']=='IFUNC' and not s['name'].startswith('__GI_')),key=lambda n:('@' in n,len(n),n))
        elif '_chk_' in canonical:
            kind='entry-adapter'
        elif canonical.startswith('__mempcpy_') and not '_small' in canonical:
            kind='entry-adapter'
        else:
            kind='body-and-paths'
        ident='x-' + canonical.split('@')[0].strip('_').replace('_','-') + ('-resolver' if kind=='resolver' else '')
        units.append(dict(unit_id=ident, kind=kind, elf=b['elf_address'], symbols=names,
                          dependencies='e06-x86-copy-lifts' if 'copy' in b['scope'] else 'e07-x86-string-lifts',
                          external_targets=b['direct_external_edges']))
    write_json(out,'unit-suggestions.json',units)
    assert len({u['unit_id'] for u in units}) == len(units)
    (out/'unit-suggestions.tsv').write_text('unit_id\tkind\telf\tsymbols\tprerequisite\n'+''.join(
        '\t'.join([u['unit_id'],u['kind'],u['elf'],';'.join(u['symbols']),u['dependencies']])+'\n' for u in units))
    comparisons = [compare_lift(REPO / 'Examples/claude' / name,elf,insns,by_address) for name in ('memcpy_amd64.v','memmove_avx_amd64.v')]
    write_json(out,'existing-lifts.json',comparisons)
    matrix = ['# Confirmed copy entry matrix', '', 'Every address is an ELF virtual address; add `0x100000` for the original Ghidra image. Exact symbol extents, byte hashes, aliases and shared-body edges are in `inventory.json`. Suffixes apply to `__<column>_<suffix>`. Equal addresses are aliases; SSSE3 memcpy and memmove entries differ. Mempcpy entries require their own return adapter.', '',
              '| Suffix | memcpy | memmove | mempcpy | memcpy_chk | memmove_chk | mempcpy_chk |',
              '|---|---|---|---|---|---|---|']
    by_name = {s['name']:s for s in selected}
    suffixes = sorted(r['implementation'].removeprefix('__memmove_') for r in declared if r['public']=='memmove')
    assert len(suffixes) == len(set(suffixes)) == 14
    for suffix in suffixes:
        names = ['__'+prefix+'_'+suffix for prefix in ('memcpy','memmove','mempcpy','memcpy_chk','memmove_chk','mempcpy_chk')]
        assert all(n in by_name for n in names)
        matrix.append('| '+suffix+' | '+' | '.join(by_name[n]['elf_address'] for n in names)+' |')
    matrix += ['', '# Subsequent string wave', '', 'These suffixes are observed debug symbols, including internal helpers and compatibility entries. Runtime-selectable candidates and CPU conditions are separately recorded in `ifunc-implementations.json`.', '', '| Family | Observed suffixes |', '|---|---|']
    for family in STRINGS+EXTRA:
        suffixes = sorted({s['name'].removeprefix('__'+family+'_') for s in selected if s['name'].startswith('__'+family+'_') and not s['name'].endswith('_ifunc')})
        matrix.append('| '+family+' | '+', '.join('`'+s+'`' for s in suffixes)+' |')
    (out/'variants.md').write_text('\n'.join(matrix)+'\n')
    # Hash relevant patched source inputs, not only upstream release source.
    source_paths = sorted((source/'sysdeps/x86_64/multiarch').glob('*'))
    source_paths += [source/'sysdeps/x86/cacheinfo.h', source/'sysdeps/x86/dl-cacheinfo.h', source/'sysdeps/x86/cpu-features.c', source/'debian/changelog', source/'debian/patches/series']
    (out/'source-files.sha256').write_text(''.join(f'{sha(p)}  {p.relative_to(source)}\n' for p in source_paths if p.is_file()))
    selector_files=sorted((source/'sysdeps/x86_64/multiarch').glob('ifunc*.h'))
    write_json(out,'source-selectors.json',[dict(file=str(p.relative_to(source)),sha256=sha(p),text=p.read_text()) for p in selector_files])
    elf_header = command('readelf','-hW',libc)+command('readelf','-lW',libc)+command('readelf','-SW',libc)
    (out/'elf-header.txt').write_text('\n'.join(line.rstrip() for line in elf_header.splitlines())+'\n')
    (out/'notes.txt').write_text(command('readelf','-n',libc))
    (out/'relocations.txt').write_text(command('readelf','-Wr',libc))
    manifest = {str(p.relative_to(root)):sha(p) for p in sorted((root/'downloads').iterdir()) if p.is_file()}
    manifest[str(libc.relative_to(root))]=sha(libc)
    manifest[str(debug.relative_to(root))]=sha(debug)
    write_json(out,'target-manifest.json',manifest)
    (out/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.name}\n' for p in sorted(out.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
    print(f'PASS: exact ELF and debug ID; {len(selected)} symbol records; {len(bodies)} extents; {len(declared)} source IFUNC entries all present')
    for comparison in comparisons:
        print(f'{comparison["file"]}: {comparison["matched_boundaries"]}/{comparison["instructions"]} boundaries, {comparison["matched_mnemonics"]}/{comparison["instructions"]} mnemonics; {len(comparison["direct_targets_outside_lift"])} external targets')


if __name__=='__main__':
    main()
