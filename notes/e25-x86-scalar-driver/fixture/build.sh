#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e25-x86-scalar-driver
here=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$state/fixture-build"
as --64 -o "$state/fixture-build/scalar.o" "$here/scalar.S"
ld -shared --build-id=sha1 -o "$state/fixture-build/scalar.so" "$state/fixture-build/scalar.o"
cmp "$here/scalar.so" "$state/fixture-build/scalar.so"
sha256sum "$state/fixture-build/scalar.so"
