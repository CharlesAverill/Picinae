Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope N.

Definition r0 := 0.
Definition r1 := 1.
Definition r5 := 5.


Definition dynamic_li_prog base_addr :=  [
  PIL_li r0 0;
  PIL_li r1 (assemble_insn (PIL_li r5 777));
  PIL_st r1 r0 (base_addr + 3 * 4)
  (* PIL_li r5 777;  <- dynamically written to memory section *)
  ].

(* Compute this then copy-paste into the file below. *)
Compute print_code_prop (dynamic_li_prog 0x00) 0x00 "dynamic_li".

Definition dynamic_li (mem:N) : Prop :=
 xbits mem 0 96 = 1816377102816974043348993.
(* We set 16 bits of execution instead of the 12 to
  enable the execution of the dynamically written instruction. *)
Definition dynamic_li_aexec (mem:N) : Prop :=
  xbits mem 0 16 = 65535.
