#!/usr/bin/env python3
"""Fresh strict extraction, closed-map publication, and prerequisite replay.

All Ghidra state is private e29. Old artifacts/receipts are read-only; their
expected implementation-hash delta is recorded separately from content checks.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

REPO = Path(__file__).resolve().parents[2]
STATE = Path('/home/charles/code/friends/.toolchains/e30-arm-ccmp')
NOTES = REPO / 'notes/e30-arm-ccmp'
ART = REPO / 'Examples/claude/lifter/scalar_ccmp'
spec = importlib.util.spec_from_file_location('e08', REPO / 'notes/e08-arm-lifts/extract.py')
e08 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e08)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def dump(p, j): p.write_text(json.dumps(j, indent=2, sort_keys=True) + '\n')


def lift(run, label, names, global_mode=True, expected=0):
    out = run / label
    cmd = [sys.executable, str(REPO / 'tools/ghidra-lifter/lift-scalar.py'), '--state', str(run / 'ghidra'), '--out', str(out)]
    if global_mode: cmd.append('--global-addressing')
    cmd += names
    print('COMMAND=' + json.dumps(cmd), flush=True)
    r = subprocess.run(cmd, capture_output=True, text=True, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    (run / f'{label}.log').write_text('COMMAND=' + json.dumps(cmd) + '\n' + r.stdout + r.stderr + f'\nEXIT_CODE={r.returncode}\n')
    print(r.stdout, end='', flush=True)
    print('EXIT_CODE=' + str(r.returncode), flush=True)
    logs = re.findall(r'Ghidra log: (.+)', r.stdout)
    if logs: shutil.copyfile(logs[-1], run / f'{label}.ghidra.log')
    if expected is not None: assert r.returncode == expected
    if r.returncode:
        assert not out.exists() and not list(run.glob('.e11-stage-*'))
    return out, r


def compare_receipt(fresh, old):
    f, o = json.loads(fresh.read_text()), json.loads(old.read_text())
    delta = {n: dict(old=o['implementation_sha256'][n], new=f['implementation_sha256'][n]) for n in f['implementation_sha256'] if f['implementation_sha256'][n] != o['implementation_sha256'][n]}
    assert set(delta) == {'pcode2coq_scalar.py'}, delta
    del f['implementation_sha256'], o['implementation_sha256']
    assert f == o, (fresh, old)
    return delta


def publish(raw, out):
    receipt = json.loads((raw / 'SUCCESS.json').read_text())
    elf = e08.ELF(e08.DEPS / 'root/lib/aarch64-linux-gnu/libc.so.6')
    dbg = e08.ELF(e08.DEPS / f'root/usr/lib/debug/.build-id/{e08.BUILD_ID[:2]}/{e08.BUILD_ID[2:]}.debug')
    assert e08.sha(elf.data) == e08.EXPECTED
    pending = {}
    for record in receipt['records']:
        old = Path(record['output']).stem
        new = old.replace('e11_', 'e30_', 1)
        text = (raw / (old + '.v')).read_text()
        assert text.count(old) == 2 and sha(raw / (old + '.v')) == record['output_sha256']
        adapted = text.replace(old, new)
        rows = json.loads((raw / (old + '.pcode.json')).read_text())
        addresses = {int(r['address'], 16) for r in rows}
        assert len(addresses) == len(rows)
        for row in rows: assert elf.at(int(row['address'], 16) - 0x100000, 4).hex() == row['bytes']
        closure = e08.control_flow(rows, addresses)
        manifest = dict(schema=1, symbol=record['symbol'], generated_program=new, record=record,
                        elf_sha256=e08.EXPECTED, debug_sha256=e08.sha(dbg.data), build_id=e08.BUILD_ID,
                        language='AARCH64:LE:64:v8A', ghidra='11.4.2', image_base='0x100000', addressing='global',
                        naming_adapter=dict(old=old, new=new, operation='identifier substitution only', occurrence_count=2),
                        implementation_sha256=receipt['implementation_sha256'],
                        harness_sha256=sha(Path(__file__)), closure=closure,
                        data=e08.data_requirements(rows, elf, e08.objects(dbg)),
                        generated_program_sha256=hashlib.sha256(adapted.encode()).hexdigest(),
                        pcode_sha256=sha(raw / (old + '.pcode.json')),
                        limits='Scalar IL/finite map closure/typing only; no function correctness, termination, or verified binary-lifter refinement.')
        pending[new + '.v'] = adapted
        pending[new + '.pcode.json'] = (raw / (old + '.pcode.json')).read_text()
        pending[new + '.manifest.json'] = json.dumps(manifest, indent=2, sort_keys=True) + '\n'
    # Publish a complete group only after byte, naming and closure checks.
    stage = out.with_name(out.name + '-stage')
    stage.mkdir()
    for n, text in pending.items(): (stage / n).write_text(text)
    stage.rename(out)
    return sorted(pending)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--run', required=True)
    a = p.parse_args()
    assert re.fullmatch('[A-Za-z0-9_-]+', a.run)
    run = STATE / a.run
    run.mkdir(parents=True, exist_ok=False)
    results = []
    for name in ('__memchr_nosimd', 'strcmp', '__strlen_asimd', 'wcschrnul', 'memcmp', 'sigandset', 'sigorset', 'sigaddset', 'sigdelset', 'sigismember'):
        raw, r = lift(run, name, [name], expected=None)
        if r.returncode:
            reason = re.sub(r'; no output accepted; Ghidra log:.*', '', r.stdout.strip())
            results.append(dict(symbol=name, status='strict-rejected', exit=r.returncode, reason=reason))
            continue
        try:
            files = publish(raw, run / (name + '-published'))
        except ValueError as e:
            results.append(dict(symbol=name, status='closure-rejected', exit=0, reason=str(e)))
            continue
        results.append(dict(symbol=name, status='supported-closed-map', exit=0, files=files))
    dump(run / 'TARGETS.json', results)

    # The unchanged e08 groups cover all 15 artifacts, including e11's global
    # copy fixture. Compare programs and raw traces byte-for-byte, then check
    # reference metadata separately. No old receipt is rewritten.
    ports = REPO / 'Examples/claude/lifter/scalar_ports'
    groups = {}
    for r in json.loads((ports / 'COVERAGE.json').read_text())['accepted']:
        groups.setdefault(tuple(r['selected_symbols']), []).append(r)
    deltas = []
    for i, (names, records) in enumerate(groups.items()):
        raw, _ = lift(run, 'reference-' + str(i), list(names))
        receipt = json.loads((raw / 'SUCCESS.json').read_text())
        for r in records:
            old = r['artifact']; name = old.replace('e08_', 'e11_', 1)
            adapted = (raw / (name + '.v')).read_text().replace(name, old)
            assert adapted == (ports / (old + '.v')).read_text(), old
            assert (raw / (name + '.pcode.json')).read_bytes() == (ports / (old + '.pcode.json')).read_bytes(), old
            m = json.loads((ports / (old + '.manifest.json')).read_text())
            rr = next(rr for rr in receipt['records'] if rr['symbol'] == r['symbol'])
            assert rr == m['record']
            delta = {n: dict(old=m['implementation_sha256'][n], new=h) for n, h in receipt['implementation_sha256'].items() if m['implementation_sha256'][n] != h}
            assert set(delta) == {'pcode2coq_scalar.py'}
            deltas.append(dict(artifact=old, content='program/raw pcode/record byte-identical', expected_metadata_delta=delta))
        if 'mempcpy' in names:
            oldroot = REPO / 'Examples/claude/lifter/scalar_global'
            for f in oldroot.iterdir():
                if f.suffix in ('.v', '.json') and f.name != 'SUCCESS.json': assert f.read_bytes() == (raw / f.name).read_bytes()
            compare_receipt(raw / 'SUCCESS.json', oldroot / 'SUCCESS.json')
    raw, _ = lift(run, 'reference-smoke', ['toascii', 'div', 'ldiv', 'swab', 'ffs', 'ffsl'], global_mode=False)
    oldroot = REPO / 'Examples/claude/lifter/scalar_smoke'
    for f in oldroot.iterdir():
        if f.suffix in ('.v', '.json') and f.name != 'SUCCESS.json': assert f.read_bytes() == (raw / f.name).read_bytes()
    delta = compare_receipt(raw / 'SUCCESS.json', oldroot / 'SUCCESS.json')
    deltas.append(dict(artifact='e11 smoke/global receipts', content='all fields except implementation hashes identical', expected_metadata_delta=delta))
    dump(run / 'REFERENCE-DELTAS.json', deltas)

    # Reviewed e29 programs and traces are also immutable reference evidence.
    root = REPO / 'Examples/claude/lifter/scalar_bitforms'
    for name in ('inet_makeaddr', 'rand_r'):
        raw, _ = lift(run, 'e29-' + name, [name])
        receipt = json.loads((raw / 'SUCCESS.json').read_text())
        old, new = 'e11_' + name + '_arm8', 'e29_' + name + '_arm8'
        assert (raw / (old + '.v')).read_text().replace(old, new) == (root / (new + '.v')).read_text()
        assert (raw / (old + '.pcode.json')).read_bytes() == (root / (new + '.pcode.json')).read_bytes()
        m = json.loads((root / (new + '.manifest.json')).read_text())
        assert receipt['records'] == [m['record']]
        delta = {n: dict(old=m['implementation_sha256'][n], new=h) for n,h in receipt['implementation_sha256'].items() if m['implementation_sha256'][n] != h}
        assert set(delta) == {'pcode2coq_scalar.py'}
        deltas.append(dict(artifact=new, content='program/raw pcode/record byte-identical', expected_metadata_delta=delta))
    dump(run / 'REFERENCE-DELTAS.json', deltas)

    # Existing seven strict publication cases, with private state/output routing.
    script = (REPO / 'notes/e11-canonical-lifter/check-failures.py').read_text()
    script = script.replace("state = pathlib.Path('/home/charles/code/friends/.toolchains/e11-canonical-lifter')", 'state = pathlib.Path(' + repr(str(run)) + ')')
    script = script.replace("'--out',str(out)", "'--state', str(state/'ghidra'), '--out',str(out)")
    exec(compile(script, 'e11-check-failures-private-state', 'exec'), {'__file__': str(REPO / 'notes/e11-canonical-lifter/check-failures.py'), '__name__': '__main__'})
    # New whole-batch failure after a successfully lowered new feature target.
    lift(run, 'reject-new-mixed', ['wcschrnul', '__strlen_asimd'], expected=1)
    print('PASS fresh targets, all 23 prerequisite artifacts, metadata deltas, and eight atomic failure batches')


if __name__ == '__main__': main()
