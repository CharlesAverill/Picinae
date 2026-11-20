#!/usr/bin/env bash
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
state=/home/charles/code/friends/.toolchains/e39-x86-backend-integration
export TMPDIR="$state/tmp" XDG_CACHE_HOME="$state/cache" DUNE_CACHE=disabled
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env dune build --root . --build-dir "$state/dune" --cache=disabled -j1 @all
