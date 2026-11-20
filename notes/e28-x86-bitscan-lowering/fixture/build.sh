#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering
here=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$state/fixture-build"
as --64 -o "$state/fixture-build/bitscan.o" "$here/bitscan.S"
ld -shared --build-id=sha1 -o "$state/fixture-build/bitscan.so" "$state/fixture-build/bitscan.o"
if [ "${1:---check}" = --update ]; then cp "$state/fixture-build/bitscan.so" "$here/bitscan.so"; fi
cmp "$here/bitscan.so" "$state/fixture-build/bitscan.so"
sha256sum "$here/bitscan.so"
