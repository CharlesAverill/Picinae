#!/usr/bin/env python3
"""Strict e08 batch: unchanged e11 supervisor, generated naming, exact evidence.

No installation, machine-semantics editing, or target execution. New run/output
paths are mandatory. Failed e11 runs never enter the published output tree.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[2]
INVENTORY = REPO / 'Examples/claude/inventory/e02-arm-inventory'
sys.path.insert(0, str(INVENTORY))
from inventory import ELF, EXPECTED, BUILD_ID, sha
DEPS = Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')
STATE = Path('/home/charles/code/friends/.toolchains/e08-arm-lifts')
ENV = '/home/charles/code/friends/.toolchains/arm-validation/picinae-env'


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def objects(elf):
    """Read OBJECT symbols too (e02's ELF.symbols intentionally selects code)."""
    result = []
    for s in elf.sections:
        if s[1] not in (2, 11):
            continue
        st = elf.sections[s[6]]
        strings = elf.data[st[4]:st[4] + st[5]]
        for off in range(s[4], s[4] + s[5], s[9]):
            n, info, _, ndx, value, size = struct.unpack_from('<IBBHQQ', elf.data, off)
            if info & 15 == 1 and ndx and size:
                result.append(dict(name=strings[n:strings.index(b'\0', n)].decode(),
                                   address=value, size=size))
    return sorted(result, key=lambda x: (x['address'], x['name']))


def control_flow(rows, addresses):
    """Check direct pcode edges, machine fallthroughs, returns; reject other exits.

    This is a finite map/edge check, not a termination or function proof.
    Raw pcode RETURN is allowed, BRANCHIND/CALLIND is never a closed return.
    """
    edges, returns = [], []
    for row in rows:
        a = int(row['address'], 16)
        terminal = False
        for op in row['pcode']:
            m = re.search(r'\b(BRANCH|CBRANCH|CALL) \(ram, 0x([0-9a-f]+), \d+\)', op)
            if m:
                kind, target = m[1], int(m[2], 16)
                if target not in addresses:
                    raise ValueError(f'dangling {kind}: {a:#x} -> {target:#x}')
                edges.append(dict(source=hex(a), kind=kind, target=hex(target)))
                terminal |= kind in ('BRANCH', 'CALL')
                if kind == 'CALL':
                    if a + 4 not in addresses:
                        raise ValueError(f'dangling call return site at {a:#x}')
                    edges.append(dict(source=hex(a), kind='call-continuation', target=hex(a + 4)))
            if re.search(r'\bRETURN ', op):
                returns.append(dict(source=hex(a), pcode=op))
                terminal = True
            if re.search(r'\b(?:BRANCHIND|CALLIND) ', op):
                raise ValueError(f'unclosed indirect transfer at {a:#x}: {op}')
        if not terminal:
            if a + 4 not in addresses:
                raise ValueError(f'dangling machine fallthrough at {a:#x}')
            edges.append(dict(source=hex(a), kind='fallthrough', target=hex(a + 4)))
    return dict(direct_and_fallthrough_edges=edges, returns=returns,
                indirect_nonreturn_edges=[], closed=True,
                meaning='finite selected machine map closes all direct edges and fallthroughs; RETURN remains caller ABI boundary')


def data_requirements(rows, elf, obs):
    """Record actual ADR/ADRP address materialization and containing ELF objects.

    Every memory-access instruction is listed, including dynamic argument/stack
    accesses. These are requirements on initial/runtime memory, never axioms.
    Pointer-bearing objects retain raw ELF bytes and loader relocation caveats.
    """
    accesses, refs = [], []
    regs = {}
    for row in rows:
        asm, addr = row['assembly'], row['address']
        if any('LOAD ' in p or ' STORE ' in p for p in row['pcode']):
            accesses.append(dict(instruction=addr, assembly=asm, pcode=[p for p in row['pcode'] if 'LOAD ' in p or ' STORE ' in p]))
        # SLEIGH prints ADRP/ADR with absolute Ghidra addresses.
        m = re.fullmatch(r'adrp?\s+(x\d+),\s*(0x[0-9a-f]+)', asm, re.I)
        if m:
            regs[m[1].lower()] = int(m[2], 16)
            continue
        m = re.fullmatch(r'add\s+(x\d+),\s*(x\d+),\s*#(0x[0-9a-f]+|\d+)', asm, re.I)
        if m and m[2].lower() in regs:
            value = regs[m[2].lower()] + int(m[3], 0)
            regs[m[1].lower()] = value
            ea = value - 0x100000
            containing = [o for o in obs if o['address'] <= ea < o['address'] + o['size']]
            exact = [o for o in containing if o['address'] == ea]
            if exact:
                containing = exact
            for o in containing:
                r = dict(symbol=o['name'], elf_address=hex(o['address']),
                         model_address=hex(o['address'] + 0x100000), size=o['size'],
                         referenced_model_address=hex(value), materialized_at=addr)
                try:
                    raw = elf.at(o['address'], o['size'])
                    r.update(file_backed=True, elf_bytes_hex=raw.hex(), elf_bytes_sha256=sha(raw))
                except ValueError:
                    r.update(file_backed=False, initialization='ELF zero-fill; mutable runtime state after initialization')
                r['relocations'] = []
                for section in elf.sections:
                    if section[1] != 4:  # SHT_RELA
                        continue
                    for off in range(section[4], section[4] + section[5], section[9]):
                        loc, info, addend = struct.unpack_from('<QQq', elf.data, off)
                        if not o['address'] <= loc < o['address'] + o['size']:
                            continue
                        rel = dict(elf_location=hex(loc), model_location=hex(loc + 0x100000),
                                   type=info & 0xffffffff, dynamic_symbol_index=info >> 32,
                                   addend=hex(addend))
                        if info & 0xffffffff == 1027:  # R_AARCH64_RELATIVE
                            rel['required_model_pointer'] = hex(addend + 0x100000)
                            try:
                                text = bytearray()
                                for i in range(4096):
                                    b = elf.at(addend + i, 1)
                                    text.extend(b)
                                    if b == b'\x00':
                                        break
                                if text[-1:] == b'\x00':
                                    rel['pointed_bytes_through_first_nul_hex'] = text.hex()
                            except ValueError:
                                pass
                        else:
                            rel['requirement'] = 'loader symbol binding required; no assumed external value'
                        r['relocations'].append(rel)
                refs.append(r)
    # Do not assert a constant-propagation completeness theorem. All raw accesses
    # remain available and selected targets receive a reviewed classification.
    unique_refs = {}
    for r in refs:
        key = (r['elf_address'], r['size'], r['referenced_model_address'])
        if key not in unique_refs:
            unique_refs[key] = r
            r['symbol_aliases'] = []
            r['materialization_sites'] = []
        dest = unique_refs[key]
        if r['symbol'] not in dest['symbol_aliases']:
            dest['symbol_aliases'].append(r['symbol'])
        if r['materialized_at'] not in dest['materialization_sites']:
            dest['materialization_sites'].append(r['materialized_at'])
    return dict(staticMemory=False, materialized_objects=list(unique_refs.values()), memory_accesses=accesses,
                contract='Map ELF virtual data addresses to model addresses by +0x100000. Runtime memory must supply these bytes/state and any relocated pointer targets; generated program does not initialize memory.',
                analysis='ADR(P)+ADD object references plus complete raw memory instruction list; manual target review required, no invented constants')


def publish_target(stage, raw, record, rows, selected, elf, dbg):
    symbol = record['symbol']
    old, new = f'e11_{symbol}_arm8', f'e08_{symbol}_arm8'
    original = (raw / f'{old}.v').read_text()
    if sha(original.encode()) != record['output_sha256'] or record['output'] != f'{old}.v':
        raise ValueError('supervisor output hash/name mismatch')
    # The sole adaptation is an identifier substitution, not an IL rewrite.
    if original.count(old) != 2:
        raise ValueError('unexpected generated identifier occurrences')
    adapted = original.replace(old, new)
    (stage / f'{new}.v').write_text(adapted)
    shutil.copyfile(raw / f'{old}.pcode.json', stage / f'{new}.pcode.json')
    addresses = {int(r['address'], 16) for r in rows}
    if len(addresses) != len(rows):
        raise ValueError('duplicate instruction addresses')
    for row in rows:
        if elf.at(int(row['address'], 16) - 0x100000, 4).hex() != row['bytes']:
            raise ValueError('instruction bytes differ from exact ELF')
    aliases = sorted({s['name'] for s in dbg.symbols() if s['address'] == int(record['elf_entry'], 16) and s['size'] == record['size']})
    sources = json.loads((raw / 'SUCCESS.json').read_text())
    manifest = dict(schema=1, symbol=symbol, generated_program=new, record=record,
                    aliases_same_entry_extent=aliases, addressing='global', image_base='0x100000',
                    selected_symbols=selected, instruction_count=len(rows),
                    elf_sha256=EXPECTED, debug_sha256=sha(dbg.data), build_id=BUILD_ID,
                    original_program_sha256=sha(original.encode()),
                    generated_program_sha256=sha(adapted.encode()),
                    pcode_sha256=sha((stage / f'{new}.pcode.json').read_bytes()),
                    naming_adapter=dict(old=old, new=new, occurrence_count=2, operation='identifier substitution only'),
                    implementation_sha256=sources['implementation_sha256'],
                    naming_closure_harness_sha256=sha(Path(__file__).read_bytes()),
                    closure=control_flow(rows, addresses),
                    data=data_requirements(rows, elf, objects(dbg)),
                    limits='Generated scalar IL and typing only; no functional correctness, termination, equivalence to historical lifts, or lifter soundness claim.')
    dump(stage / f'{new}.manifest.json', manifest)
    return dict(symbol=symbol, artifact=new, instructions=len(rows), selected_symbols=selected,
                program_sha256=manifest['generated_program_sha256'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True, help='new private run name')
    p.add_argument('--out', required=True, type=Path, help='new atomically published directory')
    p.add_argument('--priority-only', action='store_true')
    p.add_argument('--selection', type=Path, help='JSON object of exact explicit symbol-closure groups for fresh replay')
    a = p.parse_args()
    if not re.fullmatch('[A-Za-z0-9_-]+', a.run):
        p.error('unsafe run name')
    out = a.out.resolve()
    run = STATE / a.run
    if out.exists() or run.exists():
        p.error('existing output or run: stale output cannot count as success')
    run.mkdir(parents=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix='.e08-stage-', dir=out.parent))
    inventory = json.loads((INVENTORY / 'evidence/inventory.json').read_text())
    elf = ELF(DEPS / 'root/lib/aarch64-linux-gnu/libc.so.6')
    dbg = ELF(DEPS / f'root/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug')
    if sha(elf.data) != EXPECTED or sha(dbg.data) != inventory['debug_sha256']:
        raise ValueError('runtime/debug pin mismatch')
    ports = inventory['ports']
    priority = ['mempcpy', 'inet_makeaddr', 'insque', 'remque', 'wcschrnul', 'rand_r',
                'srand48_r', 'lcong48_r', 'seed48', 'a64l', 'cfmakeraw']
    groups = {n: [n] for n in priority}
    groups['mempcpy'] = ['mempcpy', '__memcpy_generic']
    groups['seed48'] = ['seed48', 'seed48_r']
    if not a.priority_only:
        for r in ports:
            if not r['lift_present'] and r['symbol'] and r['symbol']['type'] == 'FUNC':
                groups.setdefault(r['target'], [r['target']])
        for r in inventory['memory_string_symbols']:
            if re.match(r'^__(memcpy|memmove|memset|strlen|memchr)_', r['name']) and not r['name'].endswith('_ifunc') and r['type'] == 'FUNC':
                if r['name'] != '__memcpy_generic':
                    groups.setdefault(r['name'], [r['name']])
        groups.setdefault('__drand48_iterate', ['__drand48_iterate'])
    if a.selection:
        groups = json.loads(a.selection.read_text())
        if not isinstance(groups, dict) or not groups or any(not isinstance(v, list) or not v for v in groups.values()):
            p.error('selection must be nonempty label -> symbol-list object')
    accepted, rejected, attempts = [], [], []
    try:
        for label, selected in groups.items():
            raw = run / label
            command = [sys.executable, str(REPO / 'tools/ghidra-lifter/lift-scalar.py'),
                       '--state', str(STATE / 'ghidra'), '--global-addressing', '--out', str(raw), *selected]
            print('COMMAND=' + json.dumps(command), flush=True)
            result = subprocess.run(command, capture_output=True, text=True,
                                    env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
            log = 'COMMAND=' + json.dumps(command) + '\n' + result.stdout + result.stderr + f'\nEXIT_CODE={result.returncode}\n'
            (run / f'{label}.log').write_text(log)
            print(result.stdout, end='', flush=True)
            print(f'EXIT_CODE={result.returncode}', flush=True)
            ghidra_logs = re.findall(r'Ghidra log: (.+)', result.stdout)
            if ghidra_logs:
                shutil.copyfile(ghidra_logs[-1], run / f'{label}.ghidra.log')
            attempts.append(dict(target=label, selected_symbols=selected, exit=result.returncode))
            if result.returncode:
                if raw.exists():
                    raise ValueError('failed batch published output')
                rejected.append(dict(target=label, selected_symbols=selected, reason=result.stdout.strip(), driver_exit=result.returncode))
                continue
            receipt = json.loads((raw / 'SUCCESS.json').read_text())
            # Validate all members before publishing any part of a closure group.
            group_stage = run / f'{label}-adapted'
            group_stage.mkdir()
            pending = []
            try:
                for record in receipt['records']:
                    if any(x['symbol'] == record['symbol'] for x in accepted):
                        continue
                    rows = json.loads((raw / f'e11_{record["symbol"]}_arm8.pcode.json').read_text())
                    pending.append(publish_target(group_stage, raw, record, rows, selected, elf, dbg))
            except ValueError as e:
                rejected.append(dict(target=label, selected_symbols=selected, reason=f'e08 closure/data adapter: {e}', driver_exit=0))
                continue
            for f in group_stage.iterdir():
                shutil.copyfile(f, stage / f.name)
            accepted.extend(pending)
        if not accepted:
            raise ValueError('no supported artifacts: refusing an empty success publication')
        for r in rejected:
            # Keep deterministic diagnostics in the manifest; full paths/logs go
            # in unit evidence, never in the reproducible artifact content.
            r['reason'] = re.sub(r'; no output accepted; Ghidra log:.*', '', r['reason'])
        coverage = []
        for r in ports:
            n = r['target']
            ok = next((x for x in accepted if x['symbol'] == n), None)
            bad = next((x for x in rejected if n in x['selected_symbols']), None)
            status = ('historical-preserved' if r['lift_present'] else
                      'absent-exact-name' if not r['symbol'] else
                      'supported-generated' if ok else 'strict-rejected' if bad else
                      'ifunc-resolver-not-implementation' if r['symbol']['type'] == 'IFUNC' else 'not-attempted')
            resolutions = sorted({s['name'] for s in dbg.symbols() if s['name'].startswith(n + '@')}) if not r['symbol'] else []
            coverage.append(dict(target=n, e02_status=r['status'], symbol=r['symbol'], status=status, exact_versioned_names=resolutions))
        dump(stage / 'COVERAGE.json', dict(elf_sha256=EXPECTED, inventory_sha256=sha((INVENTORY / 'evidence/inventory.json').read_bytes()),
                                         ports=coverage, accepted=accepted, rejected=rejected, attempts=attempts))
        dump(stage / 'HASHES.json', {f.name: sha(f.read_bytes()) for f in sorted(stage.iterdir())})
        stage.rename(out)
        print(f'PASS e08 batch: {len(accepted)} artifacts, {len(rejected)} strict rejections; {out}', flush=True)
    finally:
        shutil.rmtree(stage, ignore_errors=True)


if __name__ == '__main__':
    main()
