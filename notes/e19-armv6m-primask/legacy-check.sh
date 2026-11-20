#!/bin/bash
# Individual old checks, retaining the exact assigned 2M cap (not old check.sh's 8M).
set -euo pipefail
ulimit -v 2000000
ulimit -s 65536
export PYTHON=/home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python
export PYTHONDONTWRITEBYTECODE=1
export OBJDUMP=arm-linux-gnueabi-objdump
out=tests/armv6m/generated
mkdir -p "$out"
arm-linux-gnueabi-as -mcpu=cortex-m0 -mthumb -o "$out/snippets.o" tests/armv6m/snippets.s
arm-linux-gnueabi-ld -Ttext=0x1000 --entry=fixture -o "$out/snippets.elf" "$out/snippets.o"
./armv6m_lifter.sh "$out/snippets.elf" fixture_bytes fixture > "$out/fixture.v"
./armv6m_lifter.sh "$out/snippets.elf" all_bytes > "$out/all_bytes.v"
rocq c -q -R _build/default Picinae -R tests/armv6m Picinae.tests.armv6m "$out/fixture.v"
rocq c -q -R _build/default Picinae -R tests/armv6m Picinae.tests.armv6m "$out/all_bytes.v"
rocq c -q -R _build/default Picinae -R tests/armv6m Picinae.tests.armv6m tests/armv6m/Checks.v
"$PYTHON" -B tests/armv6m/rejections.py "$out"
