(* A descending cursor with an exhausted position one element before a buffer. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition backward_address (p stride remaining:N):=p+stride*remaining-stride.
Lemma backward_address_zero:forall p stride,backward_address p stride 0=p-stride.
Proof. intros. unfold backward_address. rewrite N.mul_0_r,N.add_0_r. reflexivity. Qed.
Lemma backward_address_live:forall p stride i,stride<=p ->0<i ->
  backward_address p stride i=p+stride*(i-1).
Proof. intros. unfold backward_address. nia. Qed.
Lemma backward_address_bounds:forall p stride n i,
  0<stride ->stride<=p ->p+stride*n<2^32 ->i<=n+1 ->
  backward_address p stride i<2^32 /\ (backward_address p stride i<p <->i=0).
Proof.
  intros p stride n i POS BASE END COUNT. destruct (N.eq_dec i 0) as [ZERO|NONZERO].
  - subst i. rewrite backward_address_zero. split;[nia|split;[reflexivity|intro;nia]].
  - rewrite backward_address_live by nia. split;[nia|split;intro;nia].
Qed.
Lemma backward_address_step:forall p stride i,
  stride<=p ->0<i ->backward_address p stride i<2^32 ->
  msub 32 (backward_address p stride i) stride=backward_address p stride (i-1).
Proof.
  intros p stride i BASE LIVE BOUND. rewrite msub_sub by
    (rewrite backward_address_live by assumption;nia).
  rewrite N.mod_small by (unfold backward_address in *;nia).
  unfold backward_address. nia.
Qed.
Lemma backward_address_previous:forall p stride j,
  stride<=p ->p+stride*j<2^32 ->
  msub 32 (p+stride*j) stride=backward_address p stride j.
Proof.
  intros p stride j BASE BOUND. rewrite msub_sub by nia.
  rewrite N.mod_small by nia. reflexivity.
Qed.
