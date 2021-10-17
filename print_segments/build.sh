#/bin/bash

set -e

bapbuild -pkgs ppx_let,bap-elf segments.plugin && bapbundle install segments.plugin

