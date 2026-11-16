From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32 armv7_string.
Import ARM7Notations.
Open Scope N.

Definition unequal_prefix (m : memory) (p c k : N) : Prop :=
  forall i, i < k -> m Ⓑ[p+i] <> c.

Definition spread_byte32 (c : N) : N := (c * 0x01010101) mod 2^32.

Lemma land_not3 (x : N) (H : x < 2^32) : x .& (N.lnot 3 32) = x - x mod 4.
Proof.
  rewrite <- ldiff_land_low2 by lia. rewrite ldiff_sub.
  f_equal. change 3 with (N.ones 2). apply N.land_ones.
Qed.

Lemma spread_byte32_lane (c i : N) (C : c < 2^8) (I : i < 4) :
  (spread_byte32 c / 2^(8*i)) mod 2^8 = c.
Proof.
  unfold spread_byte32.
  destruct (N.eq_dec i 0) as [->|I0]; [simpl; rewrite N.div_1_r; nia|].
  destruct (N.eq_dec i 1) as [->|I1]; [nia|].
  destruct (N.eq_dec i 2) as [->|I2]; [nia|].
  destruct (N.eq_dec i 3) as [->|I3]; [nia|lia].
Qed.

Lemma xor32_lane (x y i : N) (I : i < 4) :
  ((N.lxor x y) / 2^(8*i)) mod 2^8 =
  N.lxor ((x / 2^(8*i)) mod 2^8) ((y / 2^(8*i)) mod 2^8).
Proof.
  apply N.bits_inj. intro b. destruct (N.ltb_spec b 8) as [HB|HB].
  - rewrite !N.mod_pow2_bits_low by exact HB.
    rewrite !N.div_pow2_bits.
    rewrite (N.lxor_spec x y (b+8*i)).
    rewrite (N.lxor_spec ((x / 2^(8*i)) mod 2^8)
                         ((y / 2^(8*i)) mod 2^8) b).
    rewrite !N.mod_pow2_bits_low by exact HB.
    rewrite !N.div_pow2_bits. reflexivity.
  - rewrite !N.mod_pow2_bits_high by exact HB.
    rewrite N.lxor_spec, !N.mod_pow2_bits_high by exact HB. reflexivity.
Qed.

Lemma unequal_prefix_succ (m : memory) (p c k : N) :
  unequal_prefix m p c k -> m Ⓑ[p+k] <> c -> unequal_prefix m p c (k+1).
Proof.
  intros P NZ i HI. rewrite N.add_1_r in HI.
  apply N.lt_succ_r, N.le_lteq in HI. destruct HI as [LT|EQ].
  - apply P. exact LT.
  - subst i. exact NZ.
Qed.

Lemma unequal_prefix_word (m : memory) (p c k : N) (C : c < 2^8) :
  unequal_prefix m p c k ->
  zero32 (N.lxor (m Ⓓ[p+k]) (spread_byte32 c)) = 0 ->
  unequal_prefix m p c (k+4).
Proof.
  intros P Z i HI. destruct (N.lt_ge_cases i k) as [LT|GE].
  - apply P. exact LT.
  - remember (i-k) as j. assert (EJ : i = k+j) by lia.
    assert (J : j < 4) by lia. subst i. intros E.
    apply (zero32_byte (N.lxor (m Ⓓ[p+k]) (spread_byte32 c)) j).
    + apply lxor_bound; [apply getmem_bound|].
      unfold spread_byte32. apply N.mod_lt. discriminate.
    + exact J.
    + pose proof (getmem32_byte m (p+k) j J) as G.
      replace (p+(k+j)) with (p+k+j) in E by lia.
      pose proof (spread_byte32_lane c j C J) as S.
      rewrite xor32_lane by exact J. rewrite <- G, S, E.
      apply N.lxor_nilpotent.
    + exact Z.
Qed.
