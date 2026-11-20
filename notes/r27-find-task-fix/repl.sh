#!/usr/bin/env bash
set -eu
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py --unit r27-find-task-fix --memory-kib 2500000 -- /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'ulimit -s 65536; rocq repl -q -R _build/default Picinae'
