Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv7.
Require Import memset_arm.

Import ARMNotations.
Open Scope N.
Open Scope list_scope.
Import List.ListNotations.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

Theorem strlen_nwc: forall s2 s1, memset_arm s1 = memset_arm s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog armtypctx memset_arm.
Proof.
  Picinae_typecheck.
Qed.

(* ARMv7 calling convention specifies variable registers to be preserved during calls. *)
Definition armcc_vreg :=
  [R_R4; R_R5; R_R6; R_R7; R_R8; R_R10; R_R11].
(*   v1    v2    v3    v4    v5     v7     v8*)
(* R_R9/v6 is a special case, its behavior is platform-specific *)

(* TODO: correct way to do this? *)
Definition cons_eq :
  forall {A} (x : A) xs y ys, x = y -> xs = ys -> x::xs = y::ys.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Definition arm_vreg_preserves prog :=
  forall s n s' x,
    exec_prog fh prog 0 s n s' x
    -> List.map s' armcc_vreg = List.map s armcc_vreg.

Theorem memset_preserves_vreg : arm_vreg_preserves memset_arm.
  unfold arm_vreg_preserves.
  intros.
  compute.
  repeat apply cons_eq;
    try reflexivity;
    (eapply noassign_prog_same; [|eassumption]; prove_noassign).
Qed.

Theorem memset_preserves_rsp :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_SP = s R_SP.
  intros.
  eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Theorem memset_ret :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_R0 = s R_R0.
  intros.
  eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.