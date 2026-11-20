#!/usr/bin/env bash
# Capture an exact command and its real exit status without a tee pipeline.
set -u
if (( $# < 2 )); then
    echo "Usage: $0 log-file command [argument ...]" >&2
    exit 2
fi
log=$1
shift
mkdir -p -- "$(dirname -- "$log")"
{
    printf 'CWD=%s\nCOMMAND=' "$PWD"
    separator=
    for argument in "$@"; do
        printf '%s%q' "$separator" "$argument"
        separator=' '
    done
    printf '\n'
    "$@"
    command_exit=$?
    printf '\nEXIT_CODE=%s\n' "$command_exit"
} > "$log" 2>&1
cat -- "$log"
exit "$command_exit"
