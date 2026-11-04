#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering
deps=/home/charles/code/friends/.toolchains/e02-arm-inventory
mkdir -p "$state"/{home,config,cache,tmp,projects,logs}
export HOME="$state/home" XDG_CONFIG_HOME="$state/config" XDG_CACHE_HOME="$state/cache" TMPDIR="$state/tmp"
export PYTHONDONTWRITEBYTECODE=1 JAVA_HOME="$deps/jdk-21.0.8+9" GHIDRA_INSTALL_DIR="$deps/ghidra_11.4.2_PUBLIC"
export JAVA_TOOL_OPTIONS="-Xmx1G -Duser.home=$state/home -Djava.io.tmpdir=$state/tmp"
"$deps/venv/bin/python" -m pyghidra --skip-analysis --project-path "$state/projects" --project-name fixture "$PWD/notes/e28-x86-bitscan-lowering/fixture/bitscan.so" "$PWD/notes/e28-x86-bitscan-lowering/inspect_fixture_headless.py" "$PWD" "$PWD/notes/e28-x86-bitscan-lowering/fixture-raw.json"
test -s notes/e28-x86-bitscan-lowering/fixture-raw.json
