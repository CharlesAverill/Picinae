From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_abs64.
Import ARM7Notations.
Open Scope N.

Definition neg32 (x : N) : N := 0 ⊖ x.
Definition magnitude (x : N) : N := if (x >> 31) =? 1 then neg32 x else x.
Definition apply_sign (sign q : N) : N := if sign =? 1 then neg32 q else q.
Definition quotient_sign (a b : N) : N := (N.lxor a b) >> 31.

Definition signed_quotient (a b : N) : N :=
  apply_sign (quotient_sign a b) (magnitude a / magnitude b).

Definition signed_remainder (a b : N) : N :=
  a ⊖ ((b * signed_quotient a b) mod 2^32).

Lemma sign_bound (x : N) : x < 2^32 -> (x >> 31) < 2.
Proof.
  rewrite N.shiftr_div_pow2.
  apply (N.div_lt_upper_bound x (2^31) 2); try discriminate; cbv; try lia.
Qed.

Lemma apply_sign_magnitude (x : N) :
  x < 2^32 -> apply_sign (x >> 31) (magnitude x) = x mod 2^32.
Proof.
  intros H. rewrite (N.mod_small x (2^32) H) in *.
  unfold apply_sign, magnitude, neg32. destruct ((x >> 31) =? 1);
    psimpl; reflexivity.
Qed.

Lemma magnitude_bound (x : N) : x < 2^32 -> magnitude x < 2^32.
Proof.
  unfold magnitude, neg32. destruct ((x >> 31) =? 1); psimpl; lia.
Qed.

Lemma magnitude_nonzero (x : N) : x <> 0 -> x < 2^32 -> magnitude x <> 0.
Proof.
  unfold magnitude, neg32. destruct ((x >> 31) =? 1) eqn:E; psimpl; lia.
Qed.

Lemma signed_quotient_div1 (a b : N) :
  magnitude b = 1 -> signed_quotient a b = apply_sign (quotient_sign a b) (magnitude a).
Proof.
  unfold signed_quotient. intros H. rewrite H, N.div_1_r. reflexivity.
Qed.

Lemma signed_quotient_small (a b : N) :
  magnitude a < magnitude b -> signed_quotient a b = 0.
Proof.
  unfold signed_quotient, apply_sign, neg32.
  intros H. rewrite (N.div_small _ _ H). psimpl. reflexivity.
Qed.

Lemma signed_quotient_same (a b : N) :
  magnitude b <> 0 -> magnitude a = magnitude b ->
  signed_quotient a b = apply_sign (quotient_sign a b) 1.
Proof.
  unfold signed_quotient. intros H E. rewrite E, N.div_same by exact H. reflexivity.
Qed.

Lemma signed_quotient_pow2 (a b k : N) :
  magnitude b = 2^k ->
  signed_quotient a b = apply_sign (quotient_sign a b) (magnitude a >> k).
Proof.
  unfold signed_quotient. intros H. rewrite H, <- N.shiftr_div_pow2. reflexivity.
Qed.

Lemma signed_quotient_eq (a b n mb q r : N) :
  magnitude a = n -> magnitude b = mb -> r < mb -> n = mb*q + r ->
  signed_quotient a b = apply_sign (quotient_sign a b) q.
Proof.
  unfold signed_quotient. intros NA NB HR HN.
  rewrite NA, NB, (N.div_unique n mb q r HR HN). reflexivity.
Qed.

Lemma signed_quotient_div1_original (a b : N) :
  a < 2^32 -> b < 2^32 -> magnitude b = 1 ->
  signed_quotient a b = apply_sign (b >> 31) a.
Proof.
  intros BA BB B1. rewrite signed_quotient_div1 by exact B1.
  pose proof (sign_bound a BA) as SA. pose proof (sign_bound b BB) as SB.
  unfold quotient_sign, apply_sign, magnitude, neg32.
  unfold magnitude, neg32 in B1. rewrite N.shiftr_lxor.
  assert (SA' : a >> 31 = 0 \/ a >> 31 = 1) by lia.
  assert (SB' : b >> 31 = 0 \/ b >> 31 = 1) by lia.
  destruct SA' as [SA'|SA']; destruct SB' as [SB'|SB'];
    rewrite SA'; rewrite SB' in B1 |- *; simpl in B1 |- *;
    psimpl; try reflexivity; try lia.
Qed.

Lemma land_pred_zero_power2 (b : N) :
  0 < b -> N.land b (b-1) = 0 -> b = 2^(N.log2 b).
Proof.
  intros B Z. pose proof (N.log2_spec b B) as [BL BU].
  destruct (N.eq_dec b (2^(N.log2 b))) as [E|E]; [exact E|].
  exfalso. assert (BGT : 2^(N.log2 b) < b) by lia.
  assert (BP : 0 < b-1) by lia.
  assert (Lpred : N.log2 (b-1) = N.log2 b).
  { apply N.log2_unique; [lia|]. split; lia. }
  pose proof (N.bit_log2 b ltac:(lia)) as T1.
  pose proof (N.bit_log2 (b-1) ltac:(lia)) as T2.
  rewrite Lpred in T2.
  pose proof (N.land_spec b (b-1) (N.log2 b)) as L.
  rewrite Z, T1, T2 in L. simpl in L. discriminate.
Qed.

Lemma quotient_xor_cancel (a b : N) : N.lxor (N.lxor a b) a = b.
Proof.
  rewrite N.lxor_assoc, (N.lxor_comm b a), <- N.lxor_assoc,
    N.lxor_nilpotent. apply N.lxor_0_l.
Qed.

Lemma slt32_sign (x : N) : x < 2^32 -> slt 32 x 0 = (x >> 31 =? 1).
Proof.
  intros H. pose proof (sign_bound x H) as SB.
  unfold slt. rewrite toZ_0_r, <- signbit by discriminate.
  change (N.pred 32) with 31. rewrite N.testbit_eqb, <- N.shiftr_div_pow2.
  assert (HX : x >> 31 = 0 \/ x >> 31 = 1) by lia.
  destruct HX as [HX|HX]; rewrite HX; reflexivity.
Qed.

Lemma slt32_nf (x : N) :
  x < 2^32 -> (if slt 32 x 0 then 1 else 0) = x >> 31.
Proof.
  intros H. pose proof (sign_bound x H) as SB. rewrite slt32_sign by exact H.
  assert (HX : x >> 31 = 0 \/ x >> 31 = 1) by lia.
  destruct HX as [HX|HX]; rewrite HX; reflexivity.
Qed.

Lemma neg32_eq1 (x : N) :
  x < 2^32 -> (0 ⊖ x =? 1) = (x =? 0xffffffff).
Proof.
  intros H. destruct (x =? 0xffffffff) eqn:E.
  - apply N.eqb_eq in E. subst x. reflexivity.
  - apply N.eqb_neq in E. apply N.eqb_neq. intro EQ.
    pose proof (msub_add 32 0 x) as Hadd. rewrite EQ in Hadd.
    rewrite !N.mod_small in Hadd by lia. lia.
Qed.

Lemma signmask_or_one (x : N) :
  x < 2^32 ->
  N.lor (ashiftr 32 x 31) 1 = apply_sign (x >> 31) 1.
Proof.
  intros H. rewrite ashiftr31_signmask.
  unfold signmask32, apply_sign, neg32. rewrite slt32_sign by exact H.
  destruct (x >> 31 =? 1); reflexivity.
Qed.
