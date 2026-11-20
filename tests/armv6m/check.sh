#!/bin/bash
# Run with the caller's isolated Rocq/binutils environment; install nothing.
set -euo pipefail
ulimit -v 8000000
cd "$(dirname -- "$0")/../.."
export OBJDUMP="${OBJDUMP:-arm-linux-gnueabi-objdump}"
export PYTHON="${PYTHON:-python3}"
export PYTHONDONTWRITEBYTECODE=1
out=tests/armv6m/generated
mkdir -p "$out"
arm-linux-gnueabi-as --version | head -1
"$OBJDUMP" --version | head -1
"$PYTHON" --version
"$PYTHON" -c 'import sys; print("Python executable:", sys.executable)'
arm-linux-gnueabi-as -mcpu=cortex-m0 -mthumb -o "$out/snippets.o" tests/armv6m/snippets.s
arm-linux-gnueabi-ld -Ttext=0x1000 --entry=fixture -o "$out/snippets.elf" "$out/snippets.o"
"$OBJDUMP" -d -s -t "$out/snippets.elf" > "$out/snippets.objdump"
sha256sum "$out/snippets.elf"
./armv6m_lifter.sh "$out/snippets.elf" fixture_bytes fixture > "$out/fixture.v"
./armv6m_lifter.sh "$out/snippets.elf" all_bytes > "$out/all_bytes.v"
rocq c -R . Picinae "$out/fixture.v"
rocq c -R . Picinae "$out/all_bytes.v"
rocq c -R . Picinae tests/armv6m/Checks.v
"$PYTHON" tests/armv6m/rejections.py "$out"
# Print every imported/generated/unit regression theorem's assumptions, with
# its type as a label, including the main upstream welltyped theorem.
"$PYTHON" - <<'PY'
from pathlib import Path
import re
paths = ['Picinae_armv6m.v', 'tests/armv6m/Checks.v',
         'tests/armv6m/generated/fixture.v', 'tests/armv6m/generated/all_bytes.v']
lines = ['From Stdlib Require Import NArith ZArith List.',
         'Require Import Picinae_armv6m Picinae.tests.armv6m.Checks.',
         'Require Import Picinae.tests.armv6m.generated.fixture Picinae.tests.armv6m.generated.all_bytes.']
for path in paths:
    for name in re.findall(r'^(?:Lemma|Theorem|Example) (\w+)', Path(path).read_text(), re.M):
        lines += [f'Check {name}.', f'Print Assumptions {name}.']
Path('tests/armv6m/generated/Assumptions.v').write_text('\n'.join(lines) + '\n')
PY
rocq c -R . Picinae "$out/Assumptions.v" > "$out/assumptions.log" 2>&1
