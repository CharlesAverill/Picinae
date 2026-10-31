(* finitef (AArch64 / ARMv8) -- test whether a double is NaN.
   `fmov x1,d0; mov x0,#0x7ff0000000000000; and x1,x1,#0x7fffffffffffffff;
    sub x0,x0,x1; lsr x0,x0,#0x3f; ret`.  Spec shared with amd64_finitef_proof.v
   (X0 = is_nan64 of the bit pattern).  AArch64 glibc port.
   PROVENANCE: aarch64 libc.so.6 glibc 2.35-0ubuntu3.15, symbol finitef at 0x139f00. *)

Require Import Picinae_armv8.
Require Import finitef_arm8.
Require Import arm8_common.
Require Import arm8_ieee.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem finitef_nwc: forall s2 s1, finitef_arm8 s1 = finitef_arm8 s2.
Proof. reflexivity. Qed.
Theorem finitef_welltyped: welltyped_prog arm8typctx finitef_arm8.
Proof. Picinae_typecheck. Qed.
Theorem finitef_preserves_memory:
  forall_endstates finitef_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition finitef_exit (t:trace) := match t with (Addr 20,_)::_ => true | _ => false end.
Definition postcondition (z:N) (s:store) := s R_X0 = (if is_finite32 z then 1 else 0).
Definition finitef_invs (z:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = z)
  | 20 => Some (postcondition z s)
  | _ => None
  end | _ => None end.

Theorem finitef_correct:
  forall s t s' x' z
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (Z: s R_Z0 = z),
  satisfies_all finitef_arm8 (finitef_invs z) finitef_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply finitef_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into Z.
  repeat arm8_step.
  unfold postcondition.
  rewrite shr_msub32 by
    (first [ eapply N.le_lt_trans; [apply N.land_le_r | change (2^31) with 2147483648; lia]
           | change (2^31) with 2147483648; lia ]).
  rewrite finite32_iff. reflexivity.
Qed.
