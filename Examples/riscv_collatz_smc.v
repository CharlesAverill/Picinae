Require Import NArith.
Require Import Picinae_riscv.
Require Import List.
Import ListNotations.


(*
256:    add s0, a0, x0 # mov input to s0
260:    andi t0, a0, 0x1
264:    slli t0, t0, 0x2
268:    ori t0, t0, 0xa0 # t0 is now 0xa4 if odd, or 0xa0 if even
272:    auipc t1, 0x0
276:    sb t0, 18(t1) # ---------+ Update the a0 operand to x0
                                 | if the input is even, s0, which
280:    addi a0, a0, 0x1         | holds a copy of the input, otherwise.
284:    srli a0, a0, 0x1         |
288:    add a0, s0, a0 # <-------+
292:    ret

    We assemble the above assembly using an online assembler because
    we do not have a Gallina riscv assembler. Specifically, we used
    https://riscv-simulator-five.vercel.app/
 *)

Definition collatz_riscv (s:store) : Prop :=
  Eval cbv in match List.fold_left (fun '(acc, i) code => (N.lor acc (N.shiftl code (32*i)), N.succ i))
  [ 0x00050433; 0x00157293; 0x00229293; 0x0a02e293; 0x00000317;
    0x00530923; 0x00150513; 0x00155513; 0x00a40533; 0x00008067 ]
  (0,0)
  with
  | (code, num_instructions) =>
      getmem 32 LittleE (4*num_instructions) (s V_MEM32) 256 = code
  end.

Definition collatz_riscv_aexec (mem:N) : Prop :=
  xbits mem 256 296 = N.ones 40.
