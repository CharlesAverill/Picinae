#!/usr/bin/env python3
"""Reproduce e05 per-entry lifts; never relax the reviewed e03 frontend.

Standard library only. Run using the unit's no-pip venv. Analysis of rejected
instructions is evidence only and is never used to produce a program.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUT = ROOT / 'Examples/FreeRTOS'
PIN = '5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca'
KERNEL = 'dbf70559b27d39c1fdb68dfb9a32140b6a6777a0'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def hx(n):
    return f'0x{n:08x}'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--elf', required=True, type=Path)
    parser.add_argument('--objdump', required=True, type=Path)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--check', action='store_true', help='compare regenerated artifacts without writing')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'evidence/manifest.json').read_text())
    assert digest(args.elf.read_bytes()) == PIN == manifest['artifacts']['FreeRTOS-Cortex-M0.elf']
    for name in ('layout.json', 'symbols.json'):
        assert digest((HERE / 'evidence' / name).read_bytes()) == manifest['artifacts'][name]
    for name in ('FreeRTOSConfig.h', 'fixture.ld', 'layout-probe.c', 'inputs.json'):
        assert digest((HERE / name).read_bytes()) == manifest['fixture_files'][name]
    assert digest((HERE / 'evidence/linker-map.txt').read_bytes()) == manifest['artifacts']['firmware.map']
    assert digest(gzip.decompress((HERE / 'evidence/config-macros.txt.gz').read_bytes())) == manifest['artifacts']['config-macros.txt']
    spec = importlib.util.spec_from_file_location('strict_armv6m', ROOT / 'lifter/armv6m.py')
    frontend = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(frontend)
    elf = frontend.ELF(args.elf)
    symbols = json.loads((HERE / 'evidence/symbols.json').read_text())
    funcs = {s['name']: s for s in symbols if s['kind'] == 'FUNC' and s['size']}
    objects = [s for s in symbols if s['kind'] == 'OBJECT']
    # Compare independent committed e04 disassembly before using its annotations.
    disasm = subprocess.run([str(args.objdump), '-d', '-z', str(args.elf)],
                            text=True, capture_output=True, check=True).stdout
    original = subprocess.run([str(args.objdump), '-d', '-w', str(args.elf)],
                              capture_output=True, check=True).stdout
    assert digest(original) == manifest['artifacts']['disassembly.txt']
    assert original == gzip.decompress((HERE / 'evidence/disassembly.txt.gz').read_bytes())
    decoded = {}
    for line in disasm.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{4}(?:\s+[0-9a-f]{4})?)\s+([^\s].*)$', line)
        if m:
            decoded[int(m[1], 16)] = ([int(x, 16) for x in m[2].split()], m[3])
    planned = []
    for line in (HERE / 'planned-symbols.txt').read_text().splitlines():
        fields = line.split('#', 1)[0].split()
        if fields:
            row, *names = fields
            for name in names:
                planned.append(('r41' if name == 'xTimerGenericCommandFromISR' else row, name))
    assert len(planned) == 41 and len({r for r, _ in planned}) == 41

    def owner(address):
        return [s['name'] for s in funcs.values()
                if int(s['address'], 16) <= address < int(s['address'], 16) + s['size']]

    def global_at(value):
        return [dict(name=s['name'], address=s['address'], size=s['size'],
                     offset=value - int(s['address'], 16)) for s in objects
                if int(s['address'], 16) <= value < int(s['address'], 16) + s['size']]

    analyzed = {}

    def analyze(name):
        if name in analyzed:
            return analyzed[name]
        symbol = funcs[name]
        lo = int(symbol['address'], 16)
        hi = lo + symbol['size']
        index = int(symbol['section'])
        assert int(symbol['value'], 16) == lo | 1
        assert [s for s in elf.symbols if s[0] == name and s[3] == 2] == [(name, lo | 1, symbol['size'], 2, index)]
        instructions, literals, unsupported, edges, returns, mapped_data = [], [], [], [], [], []
        a = lo
        while a < hi:
            if elf.mode(index, a) == 'd':
                mapped_data.append(dict(address=hx(a), halfword=elf.read(a, 2).hex()))
                a += 2
                continue
            assert elf.mode(index, a) == 't'
            halves, text = decoded[a]
            width = 4 if halves[0] >> 11 >= 29 else 2
            assert a + width <= hi and len(halves) * 2 == width
            assert elf.read(a, width) == b''.join(h.to_bytes(2, 'little') for h in halves)
            hw = halves[0]
            accepted = (hw & 0xf800 == 0xf000 and halves[1] & 0xd000 == 0xd000) if width == 4 else frontend.accepted16(hw)
            insn = dict(address=hx(a), opcode=' '.join(f'{h:04x}' for h in halves),
                        width=width, assembly=text, frontend_encoding_supported=accepted)
            instructions.append(insn)
            if not accepted:
                unsupported.append(insn)
            if hw & 0xf800 == 0x4800:
                pool = ((a + 4) & ~3) + (hw & 255) * 4
                word = int.from_bytes(elf.read(pool, 4, immutable=True), 'little')
                literals.append(dict(instruction=hx(a), address=hx(pool), bytes=elf.read(pool, 4).hex(),
                                     value=hx(word), imm8=hw & 255, globals=global_at(word),
                                     thumb_function_pointer=owner(word & ~1) if word & 1 else [],
                                     cortex_m_system_region=0xe0000000 <= word < 0xe0100000))
            mnemonic = text.split()[0]
            target = re.match(r'(?:bl|b(?:eq|ne|cs|cc|hs|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)?(?:\.n)?)\s+([0-9a-f]+)\s', text)
            if target:
                dest = int(target[1], 16)
                edge = dict(site=hx(a), kind='call' if mnemonic == 'bl' else 'branch',
                            target=hx(dest), owners=owner(dest), within_function=lo <= dest < hi)
                if mnemonic == 'bl':
                    edge['return_site'] = hx(a + width)
                elif mnemonic not in ('b', 'b.n'):
                    edge['fallthrough'] = hx(a + width)
                edges.append(edge)
            elif mnemonic in ('blx', 'bx') or (mnemonic in ('mov', 'add') and re.match(r'\w+\s+pc,', text)) or (mnemonic == 'pop' and 'pc' in text):
                is_return = (mnemonic == 'bx' and re.fullmatch(r'bx\s+lr', text.split(';')[0].strip()) is not None) or (mnemonic == 'pop' and 'pc' in text)
                edge = dict(site=hx(a), kind='return-candidate' if is_return else 'indirect-control',
                            assembly=text, target='runtime register/stack; Thumb bit required')
                edges.append(edge)
                if is_return:
                    returns.append(insn)
            a += width
        starts = {i['address'] for i in instructions}
        for edge in edges:
            if 'within_function' in edge:
                edge['target_is_instruction_start'] = edge['target'] in starts if edge['within_function'] else None
        sources = []
        for source in symbol['source']:
            path = args.source / source
            if source in manifest['source_files']:
                assert digest(path.read_bytes()) == manifest['source_files'][source]
                sources.append(dict(path=source, sha256=manifest['source_files'][source]))
            elif source in manifest['fixture_files']:
                sources.append(dict(path=source, sha256=manifest['fixture_files'][source]))
            else:
                sources.append(dict(path=source, provenance='see e04 compiler/linker map'))
        info = dict(symbol=name, symbol_record=symbol, source=sources, entry=hx(lo), thumb_symbol=symbol['value'],
                    end_exclusive=hx(hi), size=symbol['size'], bytes_sha256=digest(elf.read(lo, hi-lo)),
                    instructions=instructions, literals=literals, mapped_data=mapped_data,
                    unsupported_instructions=unsupported, edges=edges, return_candidates=returns)
        analyzed[name] = info
        return info

    artifacts = {}
    rows = []
    env = {**os.environ, 'OBJDUMP': str(args.objdump), 'PYTHON': sys.executable, 'PYTHONDONTWRITEBYTECODE': '1'}
    for row, name in planned:
        info = analyze(name)
        definition = name + '_armv6m'
        command = ['bash', './armv6m_lifter.sh', str(args.elf), definition, name]
        proc = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        status = 'extracted' if proc.returncode == 0 else 'rejected'
        info.update(row=row, extraction=status, command=command, exit_code=proc.returncode,
                    stderr=proc.stderr, elf_sha256=PIN)
        if proc.returncode:
            assert not proc.stdout, f'{name}: partial frontend stdout'
            assert info['unsupported_instructions'], f'{name}: unexpected non-opcode rejection: {proc.stderr}'
        else:
            assert not info['unsupported_instructions']
            assert all(e.get('target_is_instruction_start') is not False for e in info['edges'])
            text = proc.stdout
            # Additional *decode/data* checks, never a function contract.
            text += '\n(* ABI evidence only; return destinations remain dynamic. *)\n'
            text += f'Example {definition}_thumb_entry : N.odd {info["thumb_symbol"]} = true /\\\n  N.land {info["thumb_symbol"]} (N.ones 32 - 1) = start_{definition}.\nProof. vm_compute. auto. Qed.\n'
            for i, lit in enumerate(info['literals']):
                text += f'Example {definition}_literal_{i} : armv6m_literal {definition} {lit["instruction"]} {lit["imm8"]} = {lit["value"]}.\nProof. vm_compute. reflexivity. Qed.\n'
            artifacts[f'{name}_armv6m.v'] = text
            info['generated_sha256'] = digest(text.encode())
        rows.append(info)
        print(f'{row} {name}: {status}; exit={proc.returncode}; {proc.stderr.strip() or "decode/type facts generated"}')
    by_name = {r['symbol']: r for r in rows}

    def closure(name, seen):
        result = []
        for edge in analyze(name)['edges']:
            if edge['kind'] in ('return-candidate',) or edge.get('within_function'):
                continue
            if edge['kind'] == 'indirect-control' or not edge.get('owners'):
                result.append(dict(caller=name, edge=edge, prerequisite='resolve indirect/external target and its actual contract'))
                continue
            for callee in edge['owners']:
                if callee in seen:
                    continue
                seen.add(callee)
                sub = analyze(callee)
                result.append(dict(caller=name, callee=callee, site=edge['site'],
                                   extracted=callee in by_name and by_name[callee]['extraction'] == 'extracted',
                                   unsupported_instructions=sub['unsupported_instructions'],
                                   prerequisite='callee functional/ABI/frame contract; compose actual finite maps'))
                result.extend(closure(callee, seen))
        return result

    for info in rows:
        info['closure_prerequisites'] = closure(info['symbol'], {info['symbol']})
        info['blocked_helpers'] = sorted({c['callee'] for c in info['closure_prerequisites']
                                          if c.get('unsupported_instructions')})
        info['critical_isr_boundaries'] = [e for e in info['edges']
                                          if any(re.search(r'Port|InterruptMask', n) for n in e.get('owners', []))]
        info['proof_status'] = 'No function correctness proof attempted'
        artifacts[f'{info["symbol"]}.json'] = json.dumps(info, indent=2, sort_keys=True) + '\n'
    # Store reached helpers to expose precise missing instructions even below calls.
    helpers = {n: a for n, a in analyzed.items() if n not in by_name}
    helper_rejections = []
    for name, info in sorted(helpers.items()):
        if not info['unsupported_instructions']:
            continue
        command = ['bash', './armv6m_lifter.sh', str(args.elf), name + '_armv6m', name]
        proc = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        assert proc.returncode != 0 and not proc.stdout
        info.update(extraction='rejected', command=command, exit_code=proc.returncode, stderr=proc.stderr)
        helper_rejections.append(dict(symbol=name, command=command, exit_code=proc.returncode,
                                      stdout=proc.stdout, stderr=proc.stderr,
                                      unsupported_instructions=info['unsupported_instructions']))
        print(f'helper {name}: rejected; exit={proc.returncode}; {proc.stderr.strip()}; stdout empty')
    artifacts['helper-rejections.json'] = json.dumps(helper_rejections, indent=2, sort_keys=True) + '\n'
    artifacts['helpers.json'] = json.dumps(helpers, indent=2, sort_keys=True) + '\n'
    # NVIC-triggered execution is invisible in the ordinary BL call graph.
    # Inventory the actual asynchronous boundaries without adding them to the
    # set of planned/generated programs or assuming an exception contract.
    asynchronous = {}
    for name in ('SysTick_Handler', 'PendSV_Handler', 'SVC_Handler', 'vStartFirstTask'):
        info = analyze(name)
        command = ['bash', './armv6m_lifter.sh', str(args.elf), name + '_armv6m', name]
        proc = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        if proc.returncode:
            assert not proc.stdout and info['unsupported_instructions']
        else:
            assert not info['unsupported_instructions']
        info.update(command=command, exit_code=proc.returncode, stderr=proc.stderr,
                    diagnostic_only=True, generated_program_committed=False,
                    closure_prerequisites=closure(name, {name}),
                    missing_model='NVIC exception entry/return and asynchronous interference; no assumed contract')
        asynchronous[name] = info
        print(f'asynchronous boundary {name}: diagnostic strict exit={proc.returncode}; {proc.stderr.strip() or "body supported; exception/call closure unmodeled"}')
    artifacts['asynchronous-boundaries.json'] = json.dumps(asynchronous, indent=2, sort_keys=True) + '\n'
    abi = dict(elf_sha256=PIN, kernel_commit=KERNEL, release='V11.1.0',
               layout=json.loads((HERE / 'evidence/layout.json').read_text()), globals=objects,
               config_sha256=manifest['fixture_files']['FreeRTOSConfig.h'],
               config_macros_sha256=manifest['artifacts']['config-macros.txt'],
               linker_map_sha256=manifest['artifacts']['firmware.map'],
               source_tree=manifest['source_files'],
               abi=['AAPCS32: r0-r3 arguments, r0 result, stack arguments at entry SP',
                    'r4-r11 and SP callee-saved; entry SP 8-byte aligned',
                    'Thumb symbol bit is metadata; finite program addresses are even',
                    'BX/POP return needs odd Thumb LR/stack value and valid stack memory',
                    'V_MEM32 byte-addressed little endian; literal pool immutable',
                    'No interrupt/exception/interference, critical-section or scheduler contract established',
                    'vPortYield writes NVIC ICSR 0xe000ed04; memory typing does not model PendSV side effects',
                    'Finite maps contain function instruction starts only; callees require explicit composition'])
    artifacts['abi.json'] = json.dumps(abi, indent=2, sort_keys=True) + '\n'
    coverage = dict(elf_sha256=PIN, kernel_commit=KERNEL,
                    frontend_sha256=digest((ROOT / 'lifter/armv6m.py').read_bytes()),
                    extraction_driver_sha256=digest(Path(__file__).read_bytes()),
                    planned=len(rows), extracted=sum(r['extraction'] == 'extracted' for r in rows),
                    rejected=sum(r['extraction'] == 'rejected' for r in rows),
                    blocked_call_closures=sum(bool(r['blocked_helpers']) for r in rows),
                    rows=[dict(row=r['row'], symbol=r['symbol'], entry=r['entry'],
                               extraction=r['extraction'], exit_code=r['exit_code'],
                               instruction_count=len(r['instructions']), literal_count=len(r['literals']),
                               unsupported_count=len(r['unsupported_instructions']),
                               blocked_helpers=r['blocked_helpers'],
                               closure_prerequisites=len(r['closure_prerequisites'])) for r in rows])
    artifacts['coverage.json'] = json.dumps(coverage, indent=2, sort_keys=True) + '\n'
    md = ['# FreeRTOS extraction coverage', '',
          f'Exact ELF `{PIN}`. {coverage["extracted"]}/41 extracted; {coverage["rejected"]}/41 rejected.',
          f'{coverage["blocked_call_closures"]}/41 have transitive calls to strictly rejected helpers. Full e05 is PARTIAL.',
          'Extraction and kernel decode/typing checks are not functional correctness proofs.', '',
          '| Row | Function | Entry | Extraction | First strict rejection | Closure prerequisites | Rejected helpers in closure |',
          '|---|---|---|---|---|---|---|']
    for r in rows:
        failures = r['unsupported_instructions']
        first = f'`{failures[0]["address"]}: {failures[0]["opcode"]}` {failures[0]["assembly"]}' if failures else '—'
        md.append(f'| {r["row"]} | [{r["symbol"]}]({r["symbol"]}.json) | `{r["entry"]}` | {r["extraction"]} | {first} | {len(r["closure_prerequisites"])} | {", ".join(r["blocked_helpers"]) or "—"} |')
    md += ['', '## Strictly rejected reachable helpers', '',
           'Each helper was separately submitted to the unchanged e03 frontend; all exited 1 with empty stdout.', '',
           '| Helper | All missing instruction semantics (absolute address, halfword opcode, assembly) |',
           '|---|---|']
    for helper in helper_rejections:
        failures = '; '.join(f'`{i["address"]}: {i["opcode"]}` {i["assembly"]}' for i in helper['unsupported_instructions'])
        md.append(f'| {helper["symbol"]} | {failures} |')
    md += ['', 'SysTick/PendSV/SVC and first-task boundaries are inventoried separately in',
           '[asynchronous-boundaries.json](asynchronous-boundaries.json); ordinary BL edges do not close NVIC-triggered execution.']
    artifacts['coverage.md'] = '\n'.join(md) + '\n'
    supported = [r['symbol'] for r in rows if r['extraction'] == 'extracted']
    dune = '; Generated by Examples/freertos/cortex-m0/extract.py.\n'
    for name in supported:
        dune += f'(alias\n (name freertos-{name})\n (deps {name}_armv6m.vo))\n\n'
    dune += '(alias\n (name freertos-lifts)\n (deps\n' + ''.join(f'  {n}_armv6m.vo\n' for n in supported) + ' ))\n'
    artifacts['dune'] = dune
    # Root theory retains a single recursive -R mapping, as required by e00.
    root_dune = (ROOT / 'dune').read_text()
    begin, end = '; BEGIN e05 generated modules', '; END e05 generated modules'
    root_dune = re.sub(r'\n' + begin + r'.*?' + end, '', root_dune, flags=re.S)
    insertion = '\n' + begin + '\n' + ''.join(f'  Examples.FreeRTOS.{n}_armv6m\n' for n in supported) + end
    root_dune = root_dune.replace('  Examples.claude.arm8_abs_proof))', '  Examples.claude.arm8_abs_proof' + insertion + '\n ))') if begin not in root_dune else root_dune
    # Also handle subsequent runs after the marked block was removed.
    if begin not in root_dune:
        root_dune = root_dune.replace('  Examples.claude.arm8_abs_proof\n ))', '  Examples.claude.arm8_abs_proof' + insertion + '\n ))')
    assert root_dune.count(begin) == root_dune.count(end) == 1, 'root Dune module-list anchor changed'
    paths = {OUT / n: text for n, text in artifacts.items()}
    paths[ROOT / 'dune'] = root_dune
    existing = set(OUT.iterdir()) if OUT.exists() else set()
    # Never remove future hand-written armv6m_<fn>_proof.v or documentation.
    stale = {p for p in existing if p.name in {n + '_armv6m.v' for _, n in planned} and p not in paths}
    if args.check:
        assert not stale, f'stale artifacts: {stale}'
        for path, expected in paths.items():
            assert path.read_text() == expected, f'non-reproducible artifact: {path}'
        print(f'PASS: {len(paths)} artifacts reproduced byte-for-byte')
    else:
        OUT.mkdir(exist_ok=True)
        for p in stale:
            p.unlink()
        for path, text in paths.items():
            path.write_text(text)
    print(f'{coverage["extracted"]} extracted, {coverage["rejected"]} rejected; 41 individual strict frontend invocations')


if __name__ == '__main__':
    main()
