Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Require Import List.
Import ListNotations.
Open Scope N.

Definition addloop_program := [
  PIL_li 0 0; 
  PIL_addi 1 1 1; 
  PIL_subi 2 2 1; 
  PIL_beq 0 2 (-12)%Z
].

Definition p32_addloop: addr -> N :=
  p32_assemble'' 0x00 addloop_program.

(*  
Compute p32_assemble 0x00 addloop_program.
echo "     = [(0, 1); (1, 0); (2, 0); (3, 0); (4, 134); (
        5, 36); (6, 0); (7, 0); (8, 8); (9, 41); (
        10, 0); (11, 0); (12, 18); (13, 136); (
        14, 254); (15, 255)]" | tr '(' '|' | tr -d '=[)];' | sed 's/,/ =>/g; s/|/\n|/g'

*)
Definition p32_addloop' : addr -> N :=
fun a => match a with
|0 => 1 (*   PIL_li 0 0;  *)
|1 => 0
|2 => 0
|3 => 0
|4 => 134 (*   PIL_addi 1 1 1;  *)
|5 => 36
|6 => 0
|7 => 0
|8 => 8 (*   PIL_subi 2 2 1;  *)
|9 => 41
|10 => 0
|11 => 0
|12 => 18 (*   PIL_subi 2 2 1;  *)
|13 => 136
|14 => 254
|15 => 255
|_ => 0
end.