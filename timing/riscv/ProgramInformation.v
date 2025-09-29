Require Import Picinae_riscv.
Require Import NArith.

Module Type ProgramInformation.
    Parameter entry_addr : addr.
    Parameter exits : trace -> bool.
    (* Binary representation of the program to be decoded *)
    Parameter binary : addr -> N.
End ProgramInformation.
