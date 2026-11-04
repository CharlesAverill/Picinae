#!/bin/sh
set -eu
ulimit -v 8000000
# Install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune,
# cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries,
# QEMU, Python tools) go in virtual/isolated environments only: opam local
# switches, Python venvs, or Docker containers. No sudo, no apt on the host,
# no global pip/npm, no shell rc edits. Keep envs under
# /home/charles/code/friends/.toolchains/. Do not alter shared envs.
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
unit_root=/home/charles/code/friends/.toolchains/e01-x86-inventory
mkdir -p "$unit_root"
if [ ! -x "$unit_root/venv/bin/python3" ]; then
    /usr/bin/python3 -m venv --without-pip "$unit_root/venv"
fi
export PYTHONDONTWRITEBYTECODE=1 LC_ALL=C TZ=UTC
"$unit_root/venv/bin/python3" "$here/retrieve.py" "$@"
"$unit_root/venv/bin/python3" "$here/inventory.py" --root "$unit_root" --output "$here/generated"
