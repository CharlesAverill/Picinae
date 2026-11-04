#!/usr/bin/env python3
"""Retrieve/extract inert target data. Stdlib only; run inside a per-unit venv."""
import argparse
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
SNAPSHOT = 'https://snapshot.ubuntu.com/ubuntu/20251001T000000Z/'
LIBC_SHA = '9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9'
VERSION = '2.35-0ubuntu3.12'
BUILD_ID = '085164b7e9093b36e3be17226f0d94a35b818c55'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*args):
    print('+', ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), check=True, env={**os.environ, 'LC_ALL': 'C', 'TZ': 'UTC'})


def fields(text):
    result = {}
    key = None
    for line in text.splitlines():
        if line.startswith(' ') and key:
            result[key] += '\n' + line[1:]
        elif ': ' in line or line.endswith(':'):
            key, value = line.split(':', 1)
            result[key] = value.strip()
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    ap.add_argument('--offline', action='store_true')
    ap.add_argument('--keyring', type=Path, default=Path('/usr/share/keyrings/ubuntu-archive-keyring.gpg'))
    args = ap.parse_args()
    root = args.root.resolve()
    if DEFAULT_ROOT != root and DEFAULT_ROOT not in root.parents:
        ap.error('root must be the dedicated per-unit .toolchains directory or a child of it')
    downloads = root / 'downloads'
    downloads.mkdir(parents=True, exist_ok=True)
    lock = json.loads((HERE / 'downloads.lock.json').read_text())
    for item in lock:
        dest = downloads / item['name']
        if not dest.exists():
            if args.offline:
                raise FileNotFoundError(dest)
            print('+ GET', item['url'], flush=True)
            with urllib.request.urlopen(item['url'], timeout=120) as response:
                # Write atomically; never accept partial content from a failed download.
                temp = dest.with_suffix(dest.suffix + '.part')
                temp.write_bytes(response.read())
            temp.rename(dest)
        assert dest.stat().st_size == item['size'], dest
        assert sha(dest) == item['sha256'], dest
        print('SHA256 OK', item['name'], flush=True)
    gnupg = root / 'gnupg'
    gnupg.mkdir(mode=0o700, exist_ok=True)
    run('gpgv', '--homedir', gnupg, '--keyring', args.keyring, downloads / 'InRelease')
    release = fields((downloads / 'InRelease').read_text())
    release_sums = {name: (digest, int(size)) for digest, size, name in
                    (line.split() for line in release['SHA256'].splitlines() if line.strip())}
    for name, index in [('Packages.xz', 'main/binary-amd64/Packages.xz'), ('Sources.xz', 'main/source/Sources.xz')]:
        assert release_sums[index] == (sha(downloads / name), (downloads / name).stat().st_size)
    selected = {}
    for paragraph in lzma.decompress((downloads / 'Packages.xz').read_bytes()).decode().split('\n\n'):
        entry = fields(paragraph)
        if entry.get('Package') in ('libc6', 'libc6-dbg') and entry.get('Version') == VERSION:
            assert entry['Architecture'] == 'amd64'
            path = downloads / Path(entry['Filename']).name
            assert sha(path) == entry['SHA256']
            assert path.stat().st_size == int(entry['Size'])
            selected[entry['Package']] = entry
    assert set(selected) == {'libc6', 'libc6-dbg'}
    sources = [fields(p) for p in lzma.decompress((downloads / 'Sources.xz').read_bytes()).decode().split('\n\n')]
    source, = [s for s in sources if s.get('Package') == 'glibc' and s.get('Version') == VERSION]
    for line in source['Checksums-Sha256'].splitlines():
        if not line.strip():
            continue
        digest, size, name = line.split()
        assert sha(downloads / name) == digest
        assert (downloads / name).stat().st_size == int(size)
    for package, output in [('libc6', 'runtime'), ('libc6-dbg', 'debug')]:
        if not (root / output).exists():
            run('dpkg-deb', '-x', downloads / Path(selected[package]['Filename']).name, root / output)
    if not (root / 'source').exists():
        # The archive-signed Sources hash already authenticates the dsc and its members.
        run('dpkg-source', '--no-check', '-x', downloads / f'glibc_{VERSION}.dsc', root / 'source')
    libc = root / 'runtime/lib/x86_64-linux-gnu/libc.so.6'
    assert sha(libc) == LIBC_SHA
    debug = root / f'debug/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug'
    for path in (libc, debug):
        notes = subprocess.check_output(['readelf', '-n', str(path)], text=True, stderr=subprocess.DEVNULL)
        assert re.search(r'Build ID: (\w+)', notes).group(1) == BUILD_ID
    print('PASS: Ubuntu signature -> index hashes -> package/source hashes -> exact libc SHA256 and matching debug build ID')


if __name__ == '__main__':
    main()
