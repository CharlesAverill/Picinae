(* isnan (AArch64 / ARMv8) -- test whether a double is NaN.
   `fmov x1,d0; mov x0,#0x7ff0000000000000; and x1,x1,#0x7fffffffffffffff;
    sub x0,x0,x1; lsr x0,x0,#0x3f; ret`.  Spec shared with amd64_isnan_proof.v
   (X0 = is_nan64 of the bit pattern).  AArch64 glibc port.
   PROVENANCE: aarch64 libc.so.6 glibc 2.35-0ubuntu3.15, symbol isnan at 0x139f00. *)

Require Import Picinae_armv8.
Require Import isnan_arm8.
Require Import arm8_common.
Require Import arm8_ieee.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem isnan_nwc: forall s2 s1, isnan_arm8 s1 = isnan_arm8 s2.
Proof. reflexivity. Qed.
Theorem isnan_welltyped: welltyped_prog arm8typctx isnan_arm8.
Proof. Picinae_typecheck. Qed.
Theorem isnan_preserves_memory:
  forall_endstates isnan_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition isnan_exit (t:trace) := match t with (Addr 20,_)::_ => true | _ => false end.
Definition postcondition (z:N) (s:store) := s R_X0 = (if is_nan64 z then 1 else 0).
Definition isnan_invs (z:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = z)
  | 20 => Some (postcondition z s)
  | _ => None
  end | _ => None end.

Theorem isnan_correct:
  forall s t s' x' z
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (Z: s R_Z0 = z),
  satisfies_all isnan_arm8 (isnan_invs z) isnan_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isnan_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into Z.
  repeat arm8_step.
  unfold postcondition.
  rewrite shr_msub64 by (first [ change (2^63) with 9223372036854775808; lia | apply N.mod_lt; discriminate ]).
  rewrite nan64_iff. reflexivity.
Qed.
