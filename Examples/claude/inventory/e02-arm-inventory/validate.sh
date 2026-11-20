#!/usr/bin/env bash
# Existing Make/Rocq validation until the independent e00 Dune work is available.
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
REPO=$(cd -- "$HERE/../../../.." && pwd)
ENV=/home/charles/code/friends/.toolchains/arm-validation/picinae-env
cd "$REPO"
mkdir -p "$HERE/evidence"
LOG="$HERE/evidence/validation-commands.log"
: > "$LOG"
ulimit -v 8000000
run() {
  local output=$1
  shift
  local argument separator=''
  for argument in "$@"; do
    printf '%s%q' "$separator" "$argument" >> "$LOG"
    separator=' '
  done
  printf '\n' >> "$LOG"
  local result=0
  "$@" > "$HERE/evidence/$output" 2>&1 || result=$?
  printf 'exit=%s log=%s\n' "$result" "$output" >> "$LOG"
  if (( result != 0 )); then cat "$HERE/evidence/$output"; exit "$result"; fi
}
run versions.log "$ENV" bash -c 'rocq --version; ocamlc -version; dune --version; aarch64-linux-gnu-objdump --version'
run makefile.log "$ENV" rocq makefile -f _CoqProject -o Makefile.coq
run core-build.log "$ENV" make -f Makefile.coq -j1 -B Picinae_armv8.vo
run existing-lifts-typecheck.log "$ENV" bash -c 'for f in div ldiv ffs ffsl ffsll swab; do printf "CHECK %s\n" "$f"; rocq c -R . Picinae "Examples/claude/${f}_arm8.v" || exit; done'
run existing-assumptions.log "$ENV" rocq c -R . Picinae "$HERE/check_existing_assumptions.v"
run smoke-typecheck-assumptions.log "$ENV" rocq c -R . Picinae "$HERE/evidence/e02_toascii_smoke.v"
printf 'PASS bounded Make/Rocq checks; Dune verification pending e00-build\n'
