(* GrokLeaf: small arithmetic facts for straight-line leaf functions
   (Grok Bot / agent coqettu).  Written by Grok Bot (agent coqettu) and
   machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

(* "mvn w0,w0; lsr w0,w0,#31": the sign test x >= 0 on a 32-bit int. *)
Lemma lnot32_sign: ∀ x, x < 2^32 -> N.lnot x 32 >> 31 = if x <? 2^31 then 1 else 0.
Proof.
  intros x X. rewrite N.lnot_sub_low.
  - rewrite N.shiftr_div_pow2, N.ones_equiv. destruct (N.ltb_spec x (2^31)).
    + symmetry. apply (N.div_unique _ _ _ (N.pred (2^32) - x - 2^31)); lia.
    + apply N.div_small. lia.
  - destruct (N.eq_dec x 0) as [->|NZ]. reflexivity. apply N.log2_lt_pow2; lia.
Qed.

(* "ubfx x0,x0,#k,#1; eor w0,w0,#1": the negated bit test. *)
Lemma bit_not: ∀ x k, (x >> k) mod 2 .^ 1 = if N.testbit x k then 0 else 1.
Proof.
  intros x k. rewrite N.shiftr_div_pow2, <- N.testbit_spec'. destruct N.testbit; reflexivity.
Qed.

(* tbz/tbnz on bit k as psimpl leaves it. *)
Lemma bit_eqb0: ∀ x k, ((x >> k) mod 2 =? 0) = negb (N.testbit x k).
Proof.
  intros x k. rewrite N.shiftr_div_pow2, <- N.testbit_spec'. destruct N.testbit; reflexivity.
Qed.

Lemma negb_eq: ∀ b c, negb b = c -> b = negb c.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

(* Close a branch goal by rewriting the branch conditions into the spec. *)
Ltac grok_leaf_close :=
  rewrite ?bit_eqb0 in *;
  repeat match goal with H: negb _ = _ |- _ => apply negb_eq in H; simpl in H end;
  repeat match goal with H: (_ =? _) = _ |- _ => rewrite H; clear H end;
  repeat match goal with H: N.testbit _ _ = _ |- _ => rewrite H; clear H end;
  reflexivity.
