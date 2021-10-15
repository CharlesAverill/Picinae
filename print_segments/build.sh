#/bin/bash

set -e

(cd ./rewrite-test && make clean)

bapbuild -package ppx_let -package bap-elf segments.plugin && bapbundle install segments.plugin

