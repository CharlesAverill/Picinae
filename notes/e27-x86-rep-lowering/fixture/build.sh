#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e27-x86-rep-lowering/fixture-build
here=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$state"
as --64 -o "$state/rep.o" "$here/rep.S"
ld -shared --build-id=sha1 -o "$state/rep.so" "$state/rep.o"
if [[ ${1:---check} == --update ]]; then cp "$state/rep.so" "$here/rep.so"; else cmp "$state/rep.so" "$here/rep.so"; fi
sha256sum "$state/rep.so"
