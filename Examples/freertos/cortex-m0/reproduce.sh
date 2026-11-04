#!/usr/bin/env bash
set -euo pipefail
# Never install into the host or a shared toolchain. No pip packages are needed.
unit_env=${E04_ENV:-/home/charles/code/friends/.toolchains/e04-freertos-build}
case "$unit_env" in
  /home/charles/code/friends/.toolchains/e04-freertos-build|/home/charles/code/friends/.toolchains/e04-freertos-build-*) ;;
  *) echo 'E04_ENV must be a distinct e04 directory under .toolchains' >&2; exit 2 ;;
esac
mkdir -p "$unit_env"
if [[ ! -x "$unit_env/venv/bin/python3" ]]; then
  /usr/bin/python3 -m venv --without-pip "$unit_env/venv"
fi
exec "$unit_env/venv/bin/python3" "$(dirname "$(realpath "$0")")/build.py" "$unit_env" "$@"
