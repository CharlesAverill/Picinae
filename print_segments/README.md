Requirements:

bap must be installed from OPAM:
`opam install bap`

Three Python modules must be installed:
recordclass
construct
bitstruct

Process:

Build `segments` plugin for BAP:
`./build.sh`

Get the entry point, the table output and the text output:
`bap segments <binary> <table-output> <text-output> > <entry-point>`

IMPORTANT:
The `text` segment should only contain valid RV32I code, otherwise the rewriter will fail

`glue/glue.py <input-binary> <table-output> <text-output> "$(cat <entry-point>)"`
