(* copysignf (AArch64) -- float with magnitude of x and sign of y.
   `fmov; bit v0,v1,v2` (immediate sign mask).  Spec shared with amd64 (no .rodata here). *)
Require Import Picinae_armv8.
Require Import copysignf_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.
Theorem copysignf_nwc: forall s2 s1, copysignf_arm8 s1 = copysignf_arm8 s2.
Proof. reflexivity. Qed.
Theorem copysignf_welltyped: welltyped_prog arm8typctx copysignf_arm8.
Proof. Picinae_typecheck. Qed.
Definition copysignf_exit (t:trace) := match t with (Addr 8,_)::_ => true | _ => false end.
Definition postcondition (x y:N) (s:store) :=
  s R_Z0 mod 2^32 = x .& 0x7fffffff .| y .& 0x80000000.
Definition copysignf_invs (x y:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = x /\ s R_Z1 = y)
  | 8 => Some (postcondition x y s)
  | _ => None end | _ => None end.
Theorem copysignf_correct:
  forall s t s' x' x y
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s) (X: s R_Z0 = x) (Y: s R_Z1 = y),
  satisfies_all copysignf_arm8 (copysignf_invs x y) copysignf_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply copysignf_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X Y].
  repeat arm8_step.
  unfold postcondition.
  apply (copysign_insert x y 31).
Qed.
