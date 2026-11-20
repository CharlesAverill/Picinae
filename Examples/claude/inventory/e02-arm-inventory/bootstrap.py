#!/usr/bin/env python3
"""Provision only e02's isolated directory; never install host packages.

Run using an existing Python 3.12 with venv/ensurepip (e.g. the existing
Miniconda interpreter). All fetched files are hash-checked before extraction.
This does not build glibc or run any ARM target executable.
"""
import hashlib
import json
import pathlib
import subprocess
import sys
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
UNIT = pathlib.Path("/home/charles/code/friends/.toolchains/e02-arm-inventory")


def run(*args):
    print("+", *map(str, args), flush=True)
    subprocess.run(list(map(str, args)), check=True)


def main():
    if sys.version_info[:2] != (3, 12):
        raise RuntimeError("pinned wheel set requires Python 3.12")
    downloads = UNIT/"downloads"
    downloads.mkdir(parents=True, exist_ok=True)
    for item in json.loads((HERE/"artifacts.lock.json").read_text()):
        dest = downloads/item["file"]
        if not dest.exists():
            temp = dest.with_suffix(dest.suffix+".partial")
            with urllib.request.urlopen(item["url"], timeout=90) as src, temp.open("wb") as out:
                while chunk := src.read(1024*1024):
                    out.write(chunk)
            if hashlib.file_digest(temp.open("rb"), "sha256").hexdigest() != item["sha256"]:
                raise RuntimeError(f"download hash mismatch: {dest}")
            temp.rename(dest)
        with dest.open("rb") as src:
            if hashlib.file_digest(src, "sha256").hexdigest() != item["sha256"]:
                raise RuntimeError(f"cached hash mismatch: {dest}")
        print("VERIFIED", dest.name, flush=True)
    for pkg in ("libc6_2.35-0ubuntu3.15_arm64.deb", "libc6-dbg_2.35-0ubuntu3.15_arm64.deb"):
        run("dpkg-deb", "-x", downloads/pkg, UNIT/"root")
    if not (UNIT/"ghidra_11.4.2_PUBLIC").exists():
        run("unzip", "-q", downloads/"ghidra_11.4.2_PUBLIC_20250826.zip", "-d", UNIT)
    if not (UNIT/"jdk-21.0.8+9").exists():
        run("tar", "-xzf", downloads/"OpenJDK21U-jdk_x64_linux_hotspot_21.0.8_9.tar.gz", "-C", UNIT)
    if not (UNIT/"venv/bin/pip").exists():
        run(sys.executable, "-m", "venv", UNIT/"venv")
    # No dependency resolution or build isolation is needed: all wheels pinned.
    bundled = UNIT/"ghidra_11.4.2_PUBLIC/Ghidra/Features/PyGhidra/pypkg/dist/pyghidra-2.2.1-py3-none-any.whl"
    wheels = sorted(downloads.glob("*.whl"))
    run(UNIT/"venv/bin/pip", "--disable-pip-version-check", "--no-cache-dir", "install",
        "--no-index", "--no-deps", bundled, *wheels)
    source = UNIT/"source/ubuntu-glibc"
    if not source.exists():
        source.parent.mkdir(parents=True, exist_ok=True)
        run("dpkg-source", "--no-check", "-x", downloads/"glibc_2.35-0ubuntu3.15.dsc", source)
    print("PASS pinned isolated e02 toolchain provisioned")


if __name__ == "__main__":
    main()
