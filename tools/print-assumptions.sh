#!/usr/bin/env bash
# Run inside the chosen isolated Rocq/Dune environment. Never install anything.
set -euo pipefail
if (( $# < 2 )); then
    echo "Usage: $0 Picinae.path.module theorem [theorem ...]" >&2
    exit 2
fi
module=$1
shift
rocq_identifier="^[A-Za-z_][A-Za-z_0-9']*(\\.[A-Za-z_][A-Za-z_0-9']*)*$"
for identifier in "$module" "$@"; do
    if [[ ! $identifier =~ $rocq_identifier ]]; then
        echo "Invalid Rocq identifier: $identifier" >&2
        exit 2
    fi
done
if [[ $module != Picinae.* ]]; then
    echo "Expected a module below Picinae." >&2
    exit 2
fi
cd "$(git rev-parse --show-toplevel)"
ulimit -v "${PROOF_MEMORY_KB:-8000000}"
ulimit -s "${PROOF_STACK_KB:-65536}"
target=${module#Picinae.}
target=${target//.//}.vo
dune build --cache=disabled -j1 --display short "$target"
audit_tmp=$(mktemp -d "$PWD/_build/proof-audit.XXXXXXXX")
trap 'rm -rf -- "$audit_tmp"' EXIT
{
    printf 'Require Import %s.\n' "$module"
    for theorem in "$@"; do
        printf 'Check %s.%s.\nPrint Assumptions %s.%s.\n' \
            "$module" "$theorem" "$module" "$theorem"
    done
} > "$audit_tmp/Assumptions.v"
rocq compile -q -R _build/default Picinae "$audit_tmp/Assumptions.v"
