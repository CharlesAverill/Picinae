#!/bin/sh
# Kill the rocqworker compiling the given file (substring match on its args).
for p in $(pgrep -x rocqworker); do
  if tr '\0' ' ' < /proc/$p/cmdline | grep -q -- "$1"; then kill $p; fi
done
