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


Definition dynamic_li base_addr :=  [
  PIL_li r0 0;
  PIL_li r1 (assemble_insn (PIL_li r5 777));
  PIL_st r1 r0 (base_addr + 3 * 4)
  (* PIL_li r5 777;  <- dynamically written to memory section *)
  ].

Compute print_code (p32_assemble 0x00 (dynamic_li 0x00)) "p32_dynamicli"%string.

Definition p32_dynamicli : addr -> N :=
fun a => match a with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 179
  | 5 => 9
  | 6 => 3
  | 7 => 0
  | 8 => 162
  | 9 => 128
  | 10 => 1
  | 11 => 0
  | _ => 0
end.

(* A more scalable way of creating the memory. *)
Definition p32_dynamicli' := p32_assemble'' 0x00 (dynamic_li 0x00).

