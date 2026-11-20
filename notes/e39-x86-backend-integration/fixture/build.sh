#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e39-x86-backend-integration
here=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$state/fixture-build"
as --64 -o "$state/fixture-build/mixed.o" "$here/mixed.S"
ld -shared --build-id=sha1 -o "$state/fixture-build/mixed.so" "$state/fixture-build/mixed.o"
if [ "${1:---check}" = --update ]; then cp "$state/fixture-build/mixed.so" "$here/mixed.so"; else cmp "$here/mixed.so" "$state/fixture-build/mixed.so"; fi
sha256sum "$state/fixture-build/mixed.so"
