#!/usr/bin/env bash
set -euo pipefail
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r18-mutex-held-fix --memory-kib 2000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -s 65536; bash notes/r18-mutex-held/query-assumptions.sh'
