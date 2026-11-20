#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles
here=$(cd -- "$(dirname -- "$0")" && pwd)
as --64 -o "$state/fixture-build/shuffles.o" "$here/shuffles.S"
ld -shared --build-id=sha1 -o "$state/fixture-build/shuffles.so" "$state/fixture-build/shuffles.o"
cmp "$here/shuffles.so" "$state/fixture-build/shuffles.so"
sha256sum "$state/fixture-build/shuffles.so"
