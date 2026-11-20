#!/usr/bin/env bash
# Run from the repository root. Reuse tools read-only; install nothing.
set -euo pipefail
py=/home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python
runner=/home/charles/code/friends/.toolchains/arm-validation/picinae-env
fixture=/home/charles/code/friends/.toolchains/e04-freertos-build
logs=notes/e05-freertos-lifts/logs
bash tools/record-command.sh "$logs/recheck-extraction.log" "$py" -B \
  Examples/freertos/cortex-m0/extract.py \
  --elf "$fixture/verified02-a/out/FreeRTOS-Cortex-M0.elf" \
  --objdump "$fixture/arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin/arm-none-eabi-objdump" \
  --source "$fixture/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0" --check
bash tools/record-command.sh "$logs/recheck-dune-full.log" "$runner" \
  bash --noprofile --norc -e -c '
    ulimit -v 2000000
    ulimit -s 65536
    dune build --cache=disabled -j1 --display short
  '
bash tools/record-command.sh "$logs/recheck-assumptions.log" \
  env PROOF_MEMORY_KB=2000000 "$runner" "$py" -B notes/e05-freertos-lifts/check-assumptions.py
bash tools/record-command.sh "$logs/recheck-source-audit.log" "$py" -B \
  tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006
