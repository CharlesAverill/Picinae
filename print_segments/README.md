# Requirements

## Riscv-32 Toolchain
You must install [riscv32 gcc toolchains][1] toolchains to the PATH.

Example installation process:
```bash
git clone --recursive https://github.com/riscv-collab/riscv-gnu-toolchain
cd riscv-gnu-toolchain
./configure --prefix=/usr/local/ \
  --enable-linux \
  --with-arch=rv32g --with-abi=ilp32d \
  --with-target-cflags="-ffixed-t5 -ffixed-t6 -ffixed-t4" \
  --with-target-cxxflags="-ffixed-t5 -ffixed-t6 -ffixed-t4"
sudo make # Note that this step both builds and installs riscv!!!
```

## Bap
bap must be installed from OPAM: `opam install bap`

# Building and running
Build `segments` plugin for BAP: `./build.sh`

You must specify a `-i` and `-o` option to `bap riscv-cfi`

IMPORTANT: this rewriter assumes that the code sections (i.e. program bit
sections that are eXecutable) are all contiguous. This also assumes no data
within these "code" sections. These two assumptions are important for the base
rewriter to be happy (it will reject if any instructions are supposedly invalid,
even if those areas are unreachable, and are simply just data sections).

## Usage
```
NAME
       bap-riscv-cfi - rewrites Riscv32 binaries to have CFI

SYNOPSIS
       bap riscv-cfi [OPTION]...

       Rewrites Riscv32 binaries to have CFI

OPTIONS
       --handler-linux-abort
           Inserts a linux syscall to kill(getpid(), ABORT)

       --handler-none
           (default) Insert no abort handler for CFI faults

       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of `auto',
           `pager', `groff' or `plain'. With `auto', the format is `pager` or
           `plain' whenever the TERM env var is `dumb' or undefined.

       -i FILE, --input=FILE
           The input file

       -m FILE, --mapfile=FILE
           Determines wether to write out a map file describing the address
           mappings of old code locations to new code locations.

       -o FILE, --output=FILE
           The output file

       -v, --verbose
           Whether to enable verbose debugging or not

       --version
           Show version information.

```

[1]: https://github.com/riscv-collab/riscv-gnu-toolchain
