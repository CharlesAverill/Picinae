#!/bin/bash
# Strict linked-ELF frontend; run inside an isolated environment with Python 3
# and an ARM objdump. The helper uses only the Python standard library.
set -euo pipefail
exec "${PYTHON:-python3}" "$(dirname -- "$0")/lifter/armv6m.py" "$@"
