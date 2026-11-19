(* ASCII case folding and boolean classifications over abstract words. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_bits.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition ascii_upper (x:N) := (65<=?x)&&(x<=?90).
Definition ascii_lower (x:N) := (97<=?x)&&(x<=?122).
Definition ascii_alpha (x:N) := ascii_upper x || ascii_lower x.
Definition ascii_digit (x:N) := (48<=?x)&&(x<=?57).

Lemma or32_bound : forall x, x<2^32 -> N.lor x 32<2^32.
Proof.
  intros x X. destruct (N.eq_dec x 0) as [EQ|NE]; [subst; reflexivity|].
  assert (POS : 0<x) by lia.
  assert (OP : 0<N.lor x 32).
  { destruct (N.lor x 32) eqn:E; [apply N.lor_eq_0_l in E; contradiction|reflexivity]. }
  apply (proj2 (N.log2_lt_pow2 _ 32 OP)). rewrite N.log2_lor.
  apply N.max_lub_lt; [apply (proj1 (N.log2_lt_pow2 _ 32 POS)); exact X|reflexivity].
Qed.

Lemma or32_large : forall x, 128<=x -> 128<=N.lor x 32.
Proof.
  intros x X. apply N.nlt_ge. intro SMALL.
  assert (POS : 0<x) by lia.
  assert (OP : 0<N.lor x 32).
  { destruct (N.lor x 32) eqn:E; [apply N.lor_eq_0_l in E; lia|reflexivity]. }
  pose proof (proj1 (N.log2_lt_pow2 _ 7 OP) SMALL) as LOG.
  rewrite N.log2_lor in LOG.
  assert (LX : N.log2 x<7) by (eapply N.le_lt_trans; [apply N.le_max_l|exact LOG]).
  pose proof (proj2 (N.log2_lt_pow2 _ 7 POS) LX). lia.
Qed.

(* Exhaust the small ASCII domain; the high-word case stays symbolic. *)
Ltac ascii_finite x i limit :=
  first [constr_eq i limit; exfalso; lia |
    let EQ:=fresh "EQ" in let NE:=fresh "NE" in
    destruct (N.eq_dec x i) as [EQ|NE];
    [subst x; first [vm_compute; reflexivity|exfalso; lia] |
     let j:=eval vm_compute in (i+1) in ascii_finite x j limit]].

Lemma alpha_fold : forall x,
  ((97<=?N.lor x 32)&&(N.lor x 32<=?122)) = ascii_alpha x.
Proof.
  intros x. destruct (N.lt_ge_cases x 128) as [SMALL|LARGE].
  - ascii_finite x 0 128.
  - pose proof (or32_large x LARGE) as OR.
    unfold ascii_alpha, ascii_upper, ascii_lower.
    assert (A : (N.lor x 32<=?122)=false) by (apply N.leb_gt; lia).
    assert (B : (x<=?90)=false) by (apply N.leb_gt; lia).
    assert (C : (x<=?122)=false) by (apply N.leb_gt; lia).
    rewrite A,B,C. destruct (97<=?N.lor x 32), (65<=?x), (97<=?x); reflexivity.
Qed.

Lemma lowercase_or32 : forall x, ascii_upper x=true -> N.lor x 32=x+32.
Proof.
  intros x RANGE. unfold ascii_upper in RANGE. apply Bool.andb_true_iff in RANGE.
  destruct RANGE as [LO HI]. apply N.leb_le in LO, HI. ascii_finite x 0 91.
Qed.
Lemma uppercase_and95 : forall x, ascii_lower x=true -> N.land x 95=x-32.
Proof.
  intros x RANGE. unfold ascii_lower in RANGE. apply Bool.andb_true_iff in RANGE.
  destruct RANGE as [LO HI]. apply N.leb_le in LO, HI. ascii_finite x 0 123.
Qed.

Lemma boolean_or_word : forall (b c:bool),
  N.lor (if b then 1 else 0) (if c then 1 else 0) = if b||c then 1 else 0.
Proof. intros [] []; reflexivity. Qed.

Lemma ascii_upper_test : forall x, x<2^32 ->
  N.lor (if msub 32 x 65 <? 25 then 1 else 0) (if x=?90 then 1 else 0) =
    if ascii_upper x then 1 else 0.
Proof.
  intros x X. exact (classify_interval x 65 90 X ltac:(lia) ltac:(lia)).
Qed.
Lemma ascii_lower_test : forall x, x<2^32 ->
  N.lor (if msub 32 x 97 <? 25 then 1 else 0) (if x=?122 then 1 else 0) =
    if ascii_lower x then 1 else 0.
Proof.
  intros x X. exact (classify_interval x 97 122 X ltac:(lia) ltac:(lia)).
Qed.
Lemma ascii_digit_test : forall x, x<2^32 ->
  N.lor (if msub 32 x 48 <? 9 then 1 else 0) (if x=?57 then 1 else 0) =
    if ascii_digit x then 1 else 0.
Proof.
  intros x X. exact (classify_interval x 48 57 X ltac:(lia) ltac:(lia)).
Qed.
Lemma ascii_space_test : forall x, x<2^32 ->
  N.lor (if msub 32 x 9 <? 4 then 1 else 0) (if x=?13 then 1 else 0) =
    if (9<=?x)&&(x<=?13) then 1 else 0.
Proof.
  intros x X. exact (classify_interval x 9 13 X ltac:(lia) ltac:(lia)).
Qed.

Definition ascii_hex_letter (x:N) := ((65<=?x)&&(x<=?70)) || ((97<=?x)&&(x<=?102)).
Lemma hex_letter_fold : forall x,
  ((97<=?N.lor x 32)&&(N.lor x 32<=?102)) = ascii_hex_letter x.
Proof.
  intros x. destruct (N.lt_ge_cases x 128) as [SMALL|LARGE].
  - ascii_finite x 0 128.
  - pose proof (or32_large x LARGE) as OR. unfold ascii_hex_letter.
    assert (A:(N.lor x 32<=?102)=false) by (apply N.leb_gt; lia).
    assert (B:(x<=?70)=false) by (apply N.leb_gt; lia).
    assert (C:(x<=?102)=false) by (apply N.leb_gt; lia).
    rewrite A,B,C. destruct (97<=?N.lor x 32), (65<=?x), (97<=?x); reflexivity.
Qed.
Lemma ascii_hex_letter_test : forall x, x<2^32 ->
  N.lor (if msub 32 (N.lor x 32) 97 <? 5 then 1 else 0)
    (if N.lor x 32=?102 then 1 else 0) = if ascii_hex_letter x then 1 else 0.
Proof.
  intros x X. rewrite <- (hex_letter_fold x).
  exact (classify_interval (N.lor x 32) 97 102 (or32_bound x X) ltac:(lia) ltac:(lia)).
Qed.
