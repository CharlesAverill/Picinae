Requirements:

bap must be installed from OPAM:
`opam install bap`

Process:

Build `segments` plugin for BAP:
`./build.sh`

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
