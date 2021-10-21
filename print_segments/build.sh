#/bin/bash

set -e

(cd test && make clean)

bapbuild -pkgs ppx_let,bap-elf riscv_cfi.plugin && bapbundle install riscv_cfi.plugin

