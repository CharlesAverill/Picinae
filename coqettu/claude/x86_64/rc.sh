#!/bin/bash
# Compile one file with a memory cap:  ./rc.sh <file.v> [GB]
cd "$(dirname "$0")"
GB=${2:-8}
ulimit -v $((GB*1000000)); ulimit -s unlimited
rocq c -R ../../.. Picinae -R . CoqEtTu -w -deprecated-missing-stdlib -w -deprecated-syntactic-definition "$1" 2>&1 \
  | grep --line-buffered -v -E '^Warning: /home.*was$|^previously bound to Picinae|^CoqEtTu.*overriding-logical-loadpath|^bound to Picinae.coqettu|^\[overriding|^Warning: /home.*was previously$-logical-loadpath'
exit ${PIPESTATUS[0]}
