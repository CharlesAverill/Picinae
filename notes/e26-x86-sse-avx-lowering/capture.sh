#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e26-x86-sse-avx-lowering
deps=/home/charles/code/friends/.toolchains/e02-arm-inventory
kind=$1
if [ "$kind" = actual ]; then
 binary=/home/charles/code/friends/.toolchains/e01-x86-inventory/runtime/lib/x86_64-linux-gnu/libc.so.6
else
 binary=$PWD/notes/e26-x86-sse-avx-lowering/fixture/moves.so
fi
project=$(mktemp -d "$state/projects/capture.XXXXXXXX")
trap 'rm -rf -- "$project"' EXIT
rm -f -- "$PWD/notes/e26-x86-sse-avx-lowering/$kind-raw.json"
env HOME="$state/home" JAVA_HOME="$deps/jdk-21.0.8+9" GHIDRA_INSTALL_DIR="$deps/ghidra_11.4.2_PUBLIC" XDG_CONFIG_HOME="$state/config" XDG_CACHE_HOME="$state/cache" TMPDIR="$state/tmp" PYTHONDONTWRITEBYTECODE=1 JAVA_TOOL_OPTIONS="-Xmx1G -Duser.home=$state/home -Djava.io.tmpdir=$state/tmp" "$deps/venv/bin/python" -m pyghidra --skip-analysis --project-path "$project" --project-name capture "$binary" "$PWD/notes/e26-x86-sse-avx-lowering/capture.py" "$PWD" "$PWD/notes/e26-x86-sse-avx-lowering/$kind-raw.json" "$kind"

test -s "$PWD/notes/e26-x86-sse-avx-lowering/$kind-raw.json"
