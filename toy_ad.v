Require Import Picinae_toyisa Picinae_toyisa_interpreter.
Require Import List.
Import ListNotations.
Import TOYNotations.
Require Import NArith ZArith.
Open Scope N.
Open Scope bool.

Definition nop := lsl R_0 R_0 0.
Definition nopz := 0x08000000.

Definition store reg i:=
  str R_SP reg (ofZ 27 (-4*i)%Z).
Definition load rd i :=
  ldr rd R_SP (ofZ 27 (-4*i)%Z).

Definition oldpc_into reg oldpc :=
  if 2^24 <=? oldpc then None else Some (li reg oldpc).

Print List.
Definition sbb {P Q:Prop} (sum:sumbool P Q) :=
  match sum with
  | left _ => true
  | right _ => false end.
Coercion sbb : sumbool >-> bool.

(* Choose from temp registers R_3, R_4, R_5, R_2 *)
Definition tempreg1 rd rs rt :=
  if (rd == R_0) || (rs == R_0) || (rt == R_0) then
    if (rd == R_1) || (rs == R_1) || (rt == R_1) then
      if (rd == R_2) || (rs == R_2) || (rt == R_2)
      then R_3
      else R_2
    else R_1
  else R_0.

(* Choose from temp registers R_3, R_4, R_5, R_2 *)
Definition tempreg2 rd rs rt :=
  let tr1 := tempreg1 rd rs rt in
  if (tr1 == R_0) || (rd == R_0) || (rs == R_0) || (rt == R_0) then
    if (tr1 == R_1) || (rd == R_1) || (rs == R_1) || (rt == R_1) then
      if (tr1 == R_2) || (rd == R_2) || (rs == R_2) || (rt == R_2)
      then R_4
      else R_2
    else R_1
  else R_0.

Definition isreg r :=
  match r with
  | R_0 | R_1 | R_2 | R_3 | R_4 | R_5 | R_PC | R_SP => True
  | _ => False end.

Lemma temp_reg_diff:
  forall rd rs rt, isreg rd -> isreg rs -> isreg rt -> tempreg1 rd rs rt <> tempreg2 rd rs rt.
Proof.
  unfold tempreg1, tempreg2.
  intros; intro; destruct rd eqn:EQd; try contradiction; destruct rs eqn:EQs; try contradiction;
  destruct rt eqn:EQt; try contradiction; try discriminate.
Qed.

Definition chunk_add (rd rs rt:toyvar) oldpc :=
  if rd == R_PC then
    let tr1 := tempreg1 rd rs rt in
    let tr1setup := loadpctr1 <- oldpc_into tr1 oldpc;; Some [store tr1 0; loadpctr1] in
    let tr1revert := [load tr1 0] in
    (* TODO: continue here. We have a temp register tr1 which we will use for the intermediate computation.
       We need to
       1: Compute the result, of the add into tr1
       2: Check whether it falls into the old code address range
       3: If it does then translate it to the new code destination using the dynamic lookup table
       4: push the result onto the off-stack workspace
       5: restore the working registers
       6: load the computed result into PC. *)
  else
    let rs' := if rs == R_PC then tempreg1 rd rs rt else rs in
    let rssetup := if rs == R_PC then (loadpcrs <- oldpc_into rs' oldpc;; Some [store rs' 0; loadpcrs]) else Some [] in
    let rsrevert := if rs == R_PC then Some [load rs' 0] else Some [] in
    let rt' := if rt == R_PC then tempreg2 rd rs rt else rt in
    let rtsetup := if rt == R_PC then loadpcrt <- oldpc_into rt' oldpc;; Some [store rt' 1; loadpcrt] else Some [] in
    let rtrevert := if rt == R_PC then Some [load rt' 1] else Some [] in
    rssetup <- rssetup;;
    rtsetup <- rtsetup;;
    rsrevert <- rsrevert;;
    rtrevert <- rtrevert;;
    Some (rssetup++rtsetup++[add rd rs' rt']++rsrevert++rtrevert).


Fixpoint diversify zs nnops bi bi' i i2i' :=


