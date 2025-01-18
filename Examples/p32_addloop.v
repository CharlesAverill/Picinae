Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope N.

Definition addloop_program := [
  PIL_li 0 0; 
  PIL_addi 1 1 1; 
  PIL_subi 2 2 1; 
  PIL_bne 0 2 (-8)%Z
].

(* Compute this then copy-paste into the file below. *)
Compute print_code_prop addloop_program 0x00 "addloop_mem".

Definition addloop_mem (mem:N) : Prop :=
 xbits mem 0 128 = 340277338626376526927524685974490578945.
Definition addloop_mem_aexec (mem:N) : Prop :=
  xbits mem 0 16 = 65535.