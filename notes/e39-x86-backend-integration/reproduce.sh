#!/usr/bin/env bash
set -euo pipefail
state=/home/charles/code/friends/.toolchains/e39-x86-backend-integration
run=$(mktemp -d "$state/combined-replay.XXXXXXXX")
export PYTHONDONTWRITEBYTECODE=1
python3 tools/ghidra-lifter/lift-x64-integrated.py --fixture --cet-disabled --bmi1 present --abm present --out "$run/mixed" mixed
if [ "${1:---check}" = --update ]; then
 mkdir -p Examples/claude/lifter/x64_integrated_fixture
 cp "$run/mixed/"* Examples/claude/lifter/x64_integrated_fixture/
else
 diff -ru Examples/claude/lifter/x64_integrated_fixture "$run/mixed"
fi
