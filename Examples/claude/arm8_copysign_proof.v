(* copysign (AArch64) -- double with magnitude of x and sign of y.
   `fmov; bit v0,v1,v2` (immediate sign mask).  Spec shared with amd64 (no .rodata here). *)
Require Import Picinae_armv8.
Require Import copysign_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.
Theorem copysign_nwc: forall s2 s1, copysign_arm8 s1 = copysign_arm8 s2.
Proof. reflexivity. Qed.
Theorem copysign_welltyped: welltyped_prog arm8typctx copysign_arm8.
Proof. Picinae_typecheck. Qed.
Definition copysign_exit (t:trace) := match t with (Addr 12,_)::_ => true | _ => false end.
Definition postcondition (x y:N) (s:store) :=
  s R_Z0 mod 2^64 = x .& 0x7fffffffffffffff .| y .& 0x8000000000000000.
Definition copysign_invs (x y:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = x /\ s R_Z1 = y)
  | 12 => Some (postcondition x y s)
  | _ => None end | _ => None end.
Theorem copysign_correct:
  forall s t s' x' x y
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s) (X: s R_Z0 = x) (Y: s R_Z1 = y),
  satisfies_all copysign_arm8 (copysign_invs x y) copysign_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply copysign_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X Y].
  repeat arm8_step.
  unfold postcondition.
  apply (copysign_insert x y 63).
Qed.
