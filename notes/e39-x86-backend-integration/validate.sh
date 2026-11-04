#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
notes=notes/e39-x86-backend-integration
bash tools/record-command.sh "$notes/logs/finite-original.log" python3 "$notes/run-tests.py"
bash tools/record-command.sh "$notes/logs/finite-combined.log" python3 "$notes/run-tests.py" --integrated
bash tools/record-command.sh "$notes/logs/negative-original.log" python3 "$notes/old-failures.py"
bash tools/record-command.sh "$notes/logs/replay-original.log" python3 "$notes/replay-old.py"
bash tools/record-command.sh "$notes/logs/negative-combined.log" python3 "$notes/combined-failures.py"
bash tools/record-command.sh "$notes/logs/regenerate-combined.log" bash "$notes/reproduce.sh" --update
bash tools/record-command.sh "$notes/logs/replay-combined.log" bash "$notes/reproduce.sh" --check
bash tools/record-command.sh "$notes/logs/dune.log" bash "$notes/run-build.sh"
bash tools/record-command.sh "$notes/logs/22-assumptions-exact.log" /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash "$notes/print-assumptions.sh"
bash tools/record-command.sh "$notes/logs/ancestry.log" python3 "$notes/check-ancestry.py"
bash tools/record-command.sh "$notes/logs/artifact-audit.log" python3 "$notes/check-artifacts.py"
