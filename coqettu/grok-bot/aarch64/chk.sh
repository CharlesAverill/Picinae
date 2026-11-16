#!/usr/bin/env bash
# Compile .v files (memory-capped), filtering noise; exit status = coqc's.
# Usage: ./chk.sh proofs/x.v ...
cd "$(dirname "$0")"
ulimit -v ${MEMCAP:-8000000}
rc=0
for f in "$@"; do
  coqc -w -deprecated -w -level-tolerance -w -postfix-notation-not-level-1 \
    -R picinae Picinae -R lifted Grok.lifted -R lib Grok.lib -R proofs Grok.proofs "$f" 2>&1 \
    | grep -v -i 'Use "From\|for compatibility with older\|^\[deprecated\|Loading Stdlib without'
  st=${PIPESTATUS[0]}
  if [ "$st" != 0 ]; then echo "CHK FAILED ($st): $f"; rc=$st; fi
done
exit $rc
