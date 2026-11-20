#!/bin/bash
# All dependencies are reused read-only. No installs, target execution or writes to old artifacts.
set -euo pipefail
cd "$(dirname -- "$0")/../.."
ulimit -v 2000000
ulimit -s 65536
export PROOF_MEMORY_KB=2000000
export PYTHONDONTWRITEBYTECODE=1
py=/home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python
runner=/home/charles/code/friends/.toolchains/arm-validation/picinae-env
fixture=/home/charles/code/friends/.toolchains/e04-freertos-build
logs=notes/e19-armv6m-primask/logs
record() { bash tools/record-command.sh "$logs/$1" "${@:2}"; }
record final-generation.log "$py" -B notes/e19-armv6m-primask/generate.py --check
record final-frontend.log "$py" -B notes/e19-armv6m-primask/frontend-tests.py
record final-dune-mask.log "$runner" dune build --cache=disabled -j1 --display short @armv6m-primask @Examples/FreeRTOSMask/freertos-mask-lifts
record final-dune-full.log "$runner" dune build --cache=disabled -j1 --display short
record final-legacy.log "$runner" bash notes/e19-armv6m-primask/legacy-check.sh
record final-e05-compatible.log "$py" -B notes/e19-armv6m-primask/recheck-e05.py \
  --elf "$fixture/verified02-a/out/FreeRTOS-Cortex-M0.elf" \
  --objdump "$fixture/arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin/arm-none-eabi-objdump" \
  --source "$fixture/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0" --check
record final-assumptions.log "$runner" "$py" -B notes/e19-armv6m-primask/check-assumptions.py
record final-source-audit.log "$py" -B tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006
record final-provenance.log "$py" -B notes/e19-armv6m-primask/provenance.py --check
record final-diff-check.log git diff --check
