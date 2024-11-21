# README

These files are intended to help develop and test Picinae call-return functionality.

The nops.S file contains hand written assembly. Most of the functions therein are no-ops.
The calls\_test calls each function and returns.

The assembly was compiled with gcc targeted to aarch64 and therafter lifted to PIL via
our Ghidra plugin, pcode2coq.

## Compilation

Instructions to compile:
$ armgcc -S -o mylib.S mylib.c
$ armgcc -c -o mylib.o mylib.c
$ armgcc -c -o nops.o nops.S

/Users/ib/Downloads/arm-gnu-toolchain-13.3.rel1-darwin-x86_64-aarch64-none-elf/bin/aarch64-none-elf-gcc
armgcc (Arm GNU Toolchain 13.3.Rel1 (Build arm-13.24)) 13.3.1 20240614
Copyright (C) 2023 Free Software Foundation, Inc.
This is free software; see the source for copying conditions.  There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

