Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv7_lifter.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope Z.

Definition rz   := 0.
Definition r    := 1.
Definition r'   := 2.
Definition tr   := 5.
Definition rout := 0.
Definition pc   := 15.
Definition LR   := 14.
Definition always := 14. (* Uncondtional cond code *)
Definition left := 0.
Definition right := 2.

(* Receive input inp in register 0, named rz and used to store 0 in the code.
   Move inp from rz to r, load 0 into rz.
   Evaluate tr to be the code for rz if inp is even, code for r if it is odd.
   Update the final ADD instruction to add the register referred to by tr. 

   NB: The first PIL statement to execute in each instruction loads the PC
       into R_PC.

  Equivalent assembly:

    _start:
256     mov r1, r0
260     mov r0, #0
264     eor r5, r1, #1
268     strb r5, [pc, #11] ---+ Overwrite the r8 operand byte.
                              | It becomes either r or rz.
272     add r2, r1, #1        | The other bits in this byte
276     lsr r2, r2, #1        | are conveniently all zeros.
280     add r0, r2, r8   <----+
284     bx lr 

  *)

(*Compute arm_decode 0xe0820008.
Compute arm_decode 8519688.
Compute arm_decode 0x00820008.*)
Definition collatz_prog :=  [
  (* ARM_data_i (op: arm_data_op) (cond S Rn Rd imm12: Z) *)
  (* 0: *) ARM_data_i ARM_ADD always 0 rz r  0x0;
  (* 1: *) ARM_data_i ARM_MOV always 0 0  rz 0x0;
  (* 2: *) ARM_data_i ARM_AND always 0 r  tr 0x1;
  (* ARM_ls_i (op: arm_mem_op) (cond P U W Rn Rt imm12: Z) *)
  (* 3: *) ARM_ls_i ARM_STRB always 1 1 0 pc tr (4*1); (* Overwrite the last byte in instruction #6 *)
  (* Update Operands *)
  (* ARM_data_i (op: arm_data_op) (cond S Rn Rd imm12: Z) *)
  (* 4: *) ARM_data_i ARM_ADD always 0 r r' 0x1;
  (* ARM_data_r (op: arm_data_op) (cond S Rn Rd imm5 type Rm: Z) *)
  (* 5: *) ARM_data_r ARM_MOV always 0 0 r' 0x1 1 r';
  (* 6: *) ARM_data_r ARM_ADD 14 0 r' rout 0 0 0x8; (* The 0x8 gets overwritten at runtime *)
  (* End of update *)
  (* 7: *) ARM_BX always LR
  ].


Open Scope N.
Compute arm_assemble_all collatz_prog.
Compute print_code_prop 32 LittleE "V_MEM32" collatz_prog 0x100 "collatz_arm7".
Compute print_exec_prop collatz_prog 0x100 "collatz_arm7".

Definition collatz_arm7 (s:store) : Prop :=
 getmem 32 LittleE 32 (s V_MEM32) 256 = 
        101855193521039785343392224741083126283860177008767390847333957731433903558656.
Definition collatz_arm7_aexec (mem:N) : Prop :=
  xbits mem 256 288 = 4294967295.
