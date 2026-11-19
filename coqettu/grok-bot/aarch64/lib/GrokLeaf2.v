(* GrokLeaf2: extra closing helpers for bounds-checking leaf setters.
   This specification and proof were written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
Require Import NArith ZArith Lia.
Require Import Picinae_armv8.
Open Scope N_scope.

(* The "unsigned higher" flag that psimpl leaves after cmp + b.hi. *)
Lemma hi_flag: forall x k,
  (if x =? k then 0 else if k <=? x then 1 else 0) = (if x <=? k then 0 else 1).
Proof.
  intros x k.
  destruct (N.eqb_spec x k), (N.leb_spec k x), (N.leb_spec x k); lia.
Qed.

Ltac grok_leaf_close2 :=
  repeat match goal with
         | H: context[if ?x =? ?k then 0 else if ?k <=? ?x then 1 else 0] |- _ =>
             rewrite (hi_flag x k) in H
         end;
  repeat match goal with
         | H: (if ?c then _ else _) = _ |- _ => destruct c eqn:?; try discriminate H
         end;
  repeat match goal with H: ?x = ?x |- _ => clear H end;
  try match goal with |- ?s ?v = _ => match goal with H: s v = _ |- _ => rewrite H end end;
  reflexivity.

(* msub by 0 of an already-truncated value (left by cmp #0 / b.le). *)
Lemma msub_0_mod: forall w x, msub w (x mod 2^w) 0 = x mod 2^w.
Proof.
  intros w x. unfold msub.
  assert (H: 2^w <> 0) by (apply N.pow_nonzero; discriminate).
  rewrite N.mod_0_l, N.sub_0_r by exact H.
  rewrite <- N.add_mod_idemp_r, N.mod_same, N.add_0_r, N.mod_mod by exact H.
  reflexivity.
Qed.

(* The flag left by cmp #0 / b.le: Z set, or N <> V. *)
Lemma le0_flag: forall (z s: bool),
  N.lor (if z then 1 else 0) (if negb ((if s then 1 else 0) =? 0) then 1 else 0) = (if z || s then 1 else 0).
Proof. intros [|] [|]; reflexivity. Qed.

(* Case-split every branch condition left in hypotheses, discard the
   impossible cases by computation, and close by conversion. *)
Ltac grok_leaf_close3 :=
  rewrite ?N.shiftr_0_r, ?msub_0_mod in *;
  rewrite ?le0_flag in *;
  repeat match goal with H: context[if ?c then _ else _] |- _ =>
    match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end end;
  try solve [match goal with H: _ = _ |- _ => solve [cbv [N.lor negb N.eqb] in H; discriminate H] end];
  repeat match goal with
         | H: ?c = true |- context[?c] => rewrite H
         | H: ?c = false |- context[?c] => rewrite H
         end;
  try match goal with |- ?s ?v = _ => match goal with H: s v = _ |- _ => rewrite H end end;
  reflexivity.

Lemma mod_mod_pow2: forall x m n, m <= n -> (x mod 2^n) mod 2^m = x mod 2^m.
Proof.
  intros x m n H. apply N.bits_inj; intro i.
  destruct (N.ltb_spec i m).
  - rewrite !N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma scast_mod: forall w w' n, scast w w' n mod 2^w' = scast w w' n.
Proof.
  intros. unfold scast, ofZ. apply N.mod_small.
  assert (P: (0 < 2 ^ Z.of_N w')%Z) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (toZ w n) _ P) as [H1 H2].
  apply N2Z.inj_lt. rewrite Z2N.id by lia. rewrite N2Z.inj_pow. exact H2.
Qed.

