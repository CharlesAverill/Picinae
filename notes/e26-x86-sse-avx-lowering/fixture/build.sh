#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e26-x86-sse-avx-lowering
here=$(cd -- "$(dirname -- "$0")" && pwd)
as --64 -o "$state/fixture-build/moves.o" "$here/moves.S"
ld -shared --build-id=sha1 -o "$state/fixture-build/moves.so" "$state/fixture-build/moves.o"
if [ "${1:---check}" = --update ]; then cp "$state/fixture-build/moves.so" "$here/moves.so"; else cmp "$here/moves.so" "$state/fixture-build/moves.so"; fi
sha256sum "$state/fixture-build/moves.so"
