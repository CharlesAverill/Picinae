#!/usr/bin/env python3
"""Run the pinned read-only e02 dependencies with isolated e39 mutable state.

Ghidra may swallow script exceptions: trust only a fresh nonce receipt and
hash-validated complete output set. Publish a directory by atomic rename only
after validation. Failed runs remove staging, including partial .v files.
"""
import argparse
import fcntl
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import uuid
from x64_provenance import dependency_manifest, feature_profile

DEFAULT_DEPS = '/home/charles/code/friends/.toolchains/e02-arm-inventory'
DEFAULT_STATE = '/home/charles/code/friends/.toolchains/e39-x86-backend-integration'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_receipt(stage, token, symbols, elf_sha, kind, profile):
    receipt = json.loads((stage/'SUCCESS.json').read_text())
    if receipt['token'] != token or [r['symbol'] for r in receipt['records']] != symbols:
        raise ValueError('incomplete or stale success receipt')
    if receipt.get('elf_sha256') != elf_sha or receipt.get('source_kind') != kind or receipt.get('profile') != profile or receipt.get('language') != 'x86:LE:64:default' or receipt.get('addressing') != 'global':
        raise ValueError('source/profile/language receipt mismatch')
    if receipt.get('features') != feature_profile(profile) or receipt.get('semantics') != 'scalar-copy256-rep-scan-sequential-v1':
        raise ValueError('feature/semantics mismatch')
    if receipt.get('dependencies') != dependency_manifest(pathlib.Path(__file__).resolve().parents[2], kind):
        raise ValueError('transitive dependency closure mismatch')
    if receipt.get('scope') != 'closed-selected-function-extents':
        raise ValueError('scope receipt mismatch')
    expected = {'SUCCESS.json'}
    for r in receipt['records']:
        name = f'e39_{r["symbol"]}_amd64'
        expected.update({name+'.v', name+'.pcode.json'})
        if r['output'] != name+'.v' or digest(stage/r['output']) != r['output_sha256'] or r['instructions'] <= 0 or digest(stage/(name+'.pcode.json')) != r['pcode_sha256']:
            raise ValueError('output validation failure')
    if {f.name for f in stage.iterdir()} != expected or any(not f.is_file() or f.is_symlink() for f in stage.iterdir()):
        raise ValueError('unexpected or missing outputs')
    return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--deps', type=pathlib.Path, default=pathlib.Path(DEFAULT_DEPS))
    p.add_argument('--state', type=pathlib.Path, default=pathlib.Path(DEFAULT_STATE))
    p.add_argument('--out', type=pathlib.Path, required=True, help='new output directory (must not exist)')
    p.add_argument('--inventory', type=pathlib.Path, default=pathlib.Path('/home/charles/code/friends/.toolchains/e01-x86-inventory'))
    p.add_argument('--cet-disabled', action='store_true', help='explicit sequential profile: IBT and shadow stacks disabled; exact ENDBR64 becomes Nop')
    p.add_argument('--fixture', action='store_true', help='use the pinned synthetic mixed fixture, never glibc')
    p.add_argument('--bmi1', choices=('present','absent'), default='unspecified')
    p.add_argument('--abm', choices=('present','absent'), default='unspecified', help='CPUID LZCNT/ABM feature bit')
    p.add_argument('symbols', nargs='+')
    a = p.parse_args()
    kind = 'synthetic' if a.fixture else 'glibc'
    profile = ('integrated-cet-disabled' if a.cet_disabled else 'integrated-strict') + ';bmi1=' + a.bmi1 + ';abm=' + a.abm
    repo = pathlib.Path(__file__).resolve().parents[2]
    if a.out.exists() or a.out.is_symlink():
        p.error('output directory already exists; refusing stale/replaced output')
    a.deps, a.state, a.out = (x.resolve() for x in (a.deps, a.state, a.out))
    if a.state != pathlib.Path(DEFAULT_STATE).resolve() or a.state not in a.out.parents:
        p.error('all mutable state/output must stay under the e39 toolchain root')
    if a.out.exists() or a.out.is_symlink():
        p.error('output directory already exists; refusing stale/replaced output')
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n) for n in a.symbols) or len(set(a.symbols)) != len(a.symbols):
        p.error('symbols must be distinct C identifiers')
    if a.state == a.deps or a.deps in a.state.parents or a.deps == a.out or a.deps in a.out.parents:
        p.error('dependency tree is read-only')
    source = repo/'Examples/claude/inventory/e02-arm-inventory'
    lock = json.loads((source/'artifacts.lock.json').read_text())
    # Verify the exact runtime/debug, Ghidra and JDK release archives used by e02.
    for item in lock:
        artifact = a.deps/'downloads'/item['file']
        if digest(artifact) != item['sha256']:
            raise ValueError(f'dependency archive pin mismatch: {artifact}')
    isa_pins = json.loads((repo/'notes/e25-x86-scalar-driver/isa-pins.json').read_text())
    for f, sha in isa_pins.items():
        if digest(a.deps/f) != sha:
            raise ValueError(f'x86 SLEIGH pin mismatch: {f}')
    invsource = repo/'Examples/claude/inventory/e01-x86-inventory'
    invlock = json.loads((invsource/'generated/target-manifest.json').read_text())
    a.inventory = a.inventory.resolve()
    for f, sha in invlock.items():
        if digest(a.inventory/f) != sha:
            raise ValueError(f'x86 inventory pin mismatch: {f}')
    binary = a.inventory/'runtime/lib/x86_64-linux-gnu/libc.so.6'
    if a.fixture:
        binary = repo/'notes/e39-x86-backend-integration/fixture/mixed.so'
        pins = json.loads((binary.parent/'pins.json').read_text())
        if digest(binary) != pins['sha256']:
            raise ValueError('synthetic fixture pin mismatch')
    if a.state == a.inventory or a.inventory in a.state.parents or a.inventory == a.out or a.inventory in a.out.parents:
        p.error('inventory is read-only')
    for part in ('home', 'config', 'cache', 'tmp', 'projects', 'logs'):
        (a.state/part).mkdir(parents=True, exist_ok=True)
    lockfile = (a.state/'run.lock').open('w')
    fcntl.flock(lockfile, fcntl.LOCK_EX | fcntl.LOCK_NB)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    dependencies = dependency_manifest(repo, kind)
    token = uuid.uuid4().hex
    stage = pathlib.Path(tempfile.mkdtemp(prefix='.e39-stage-', dir=a.out.parent))
    project = pathlib.Path(tempfile.mkdtemp(prefix='lift-', dir=a.state/'projects'))
    logfile = a.state/'logs'/f'{token}.log'
    env = os.environ.copy()
    java = a.deps/'jdk-21.0.8+9'
    env.update(HOME=str(a.state/'home'), JAVA_HOME=str(java),
               GHIDRA_INSTALL_DIR=str(a.deps/'ghidra_11.4.2_PUBLIC'),
               XDG_CONFIG_HOME=str(a.state/'config'), XDG_CACHE_HOME=str(a.state/'cache'),
               TMPDIR=str(a.state/'tmp'), PYTHONDONTWRITEBYTECODE='1',
               JAVA_TOOL_OPTIONS=f'-Xmx1G -Duser.home={a.state / "home"} -Djava.io.tmpdir={a.state / "tmp"}',
               PATH=f'{a.deps / "venv/bin"}:{java / "bin"}:{env["PATH"]}')
    # Ignore inherited Java injection options; enforce the bounded local JVM.
    env.pop('PYTHONPATH', None)
    env.pop('PYTHONHOME', None)
    env.pop('_JAVA_OPTIONS', None)
    env.pop('JDK_JAVA_OPTIONS', None)
    command = [str(a.deps/'venv/bin/python'), '-m', 'pyghidra', '--skip-analysis',
               '--project-path', str(project), '--project-name', 'e39', str(binary),
               str(repo/'tools/ghidra-lifter/x64_integrated_headless.py'), str(repo), str(stage),
               str(a.inventory), token, kind, profile, *a.symbols]
    try:
        app_log = a.state/'config/charles-ghidra/ghidra_11.4.2_PUBLIC/application.log'
        app_offset = app_log.stat().st_size if app_log.exists() else 0
        with logfile.open('w') as log:
            log.write('COMMAND='+json.dumps(command)+'\nJAVA_TOOL_OPTIONS='+env['JAVA_TOOL_OPTIONS']+'\n')
            log.flush()
            run = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
            log.write(f'\nLAUNCHER_EXIT={run.returncode}\n')
            if app_log.exists():
                with app_log.open() as app:
                    app.seek(app_offset)
                    log.write(app.read())
        if run.returncode:
            raise ValueError(f'Ghidra launcher exit {run.returncode}')
        if not (stage/'SUCCESS.json').is_file():
            errors = re.findall(r'^.*(?:Unsupported:|ValueError:).+$', logfile.read_text(), re.M)
            detail = errors[-1][:500] if errors else 'missing fresh success receipt'
            raise ValueError(f'Ghidra script failed: {detail}')
        receipt = validate_receipt(stage, token, a.symbols, digest(binary), kind, profile)
        if receipt.get('dependencies') != dependencies or dependency_manifest(repo, kind) != dependencies:
            raise ValueError('transitive dependency closure changed during extraction')
        receipt['isa_sha256'] = isa_pins
        # Receipt token is a freshness check, not reproducible artifact content.
        del receipt['token']
        (stage/'SUCCESS.json').write_text(json.dumps(receipt, indent=2)+'\n')
        # Serialize publishers to the same destination and recheck after launch.
        with (a.out.parent/'.e39-publish.lock').open('a') as publish_lock:
            fcntl.flock(publish_lock, fcntl.LOCK_EX)
            if a.out.exists() or a.out.is_symlink():
                raise ValueError('output appeared during run')
            stage.rename(a.out)
        print(f'PASS {len(a.symbols)} hash-validated complete artifacts: {a.out}')
    except Exception as e:
        print(f'FAIL {e}; no output accepted; Ghidra log: {logfile}')
        return 1
    finally:
        shutil.rmtree(stage, ignore_errors=True)
        shutil.rmtree(project, ignore_errors=True)
    print(f'Ghidra log: {logfile}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
