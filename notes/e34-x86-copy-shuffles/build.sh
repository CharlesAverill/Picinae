#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles
export XDG_CACHE_HOME="$state/cache" TMPDIR="$state/tmp"
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env dune build --root "$PWD" --build-dir "$state/dune-build" --cache=disabled -j1
