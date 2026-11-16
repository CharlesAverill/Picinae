From Stdlib Require Import NArith.
Require Import Picinae_armv7.
Import ARM7Notations.
Open Scope N.

Definition zero32 (x : N) : N :=
  ((x ⊖ 0x01010101) .& (N.lnot x 32)) .& 0x80808080.

Ltac zero32_bit j :=
  unfold zero32;
  rewrite !N.land_spec, N.lnot_spec_low by lia;
  change (N.testbit 0x80808080 j) with true;
  rewrite !Bool.andb_true_r;
  apply Bool.andb_true_iff; split;
  [ rewrite N.testbit_true; unfold msub;
    replace (0x01010101 mod 2^32) with 0x01010101 by reflexivity;
    nia
  | rewrite N.testbit_eqb; nia ].

Lemma zero32_byte0 (x : N) (H : x < 2^32) :
  x mod 2^8 = 0 -> zero32 x <> 0.
Proof.
  intros B Z. assert (HB : N.testbit (zero32 x) 7 = true) by zero32_bit 7.
  rewrite Z in HB. discriminate.
Qed.

Lemma zero32_byte1 (x : N) (H : x < 2^32) :
  (x / 2^8) mod 2^8 = 0 -> zero32 x <> 0.
Proof.
  intros B Z. assert (HB : N.testbit (zero32 x) 15 = true) by zero32_bit 15.
  rewrite Z in HB. discriminate.
Qed.

Lemma zero32_byte2 (x : N) (H : x < 2^32) :
  (x / 2^16) mod 2^8 = 0 -> zero32 x <> 0.
Proof.
  intros B Z. assert (HB : N.testbit (zero32 x) 23 = true) by zero32_bit 23.
  rewrite Z in HB. discriminate.
Qed.

Lemma zero32_byte3 (x : N) (H : x < 2^32) :
  (x / 2^24) mod 2^8 = 0 -> zero32 x <> 0.
Proof.
  intros B Z. assert (HB : N.testbit (zero32 x) 31 = true) by zero32_bit 31.
  rewrite Z in HB. discriminate.
Qed.

Lemma zero32_byte (x i : N) (H : x < 2^32) (I : i < 4) :
  (x / 2^(8*i)) mod 2^8 = 0 -> zero32 x <> 0.
Proof.
  intros B. destruct (N.eq_dec i 0) as [->|I0].
  - simpl in B. rewrite N.div_1_r in B. apply zero32_byte0; assumption.
  - destruct (N.eq_dec i 1) as [->|I1].
    + apply zero32_byte1; assumption.
    + destruct (N.eq_dec i 2) as [->|I2].
      * apply zero32_byte2; assumption.
      * destruct (N.eq_dec i 3) as [->|I3].
        -- apply zero32_byte3; assumption.
        -- lia.
Qed.
