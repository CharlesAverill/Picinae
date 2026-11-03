#!/usr/bin/env bash
set -eu
attempt=$1
cp Examples/claude/arm8_ffsl_proof.v "notes/a-ffsl-fix/attempt-$attempt.v.txt"
exec bash tools/record-command.sh "notes/a-ffsl-fix/build-$attempt.log" bash notes/a-ffsl-fix/build.sh
