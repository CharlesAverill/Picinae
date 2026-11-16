From Stdlib Require Import NArith.
Require Import Picinae_armv7.
Import ARM7Notations.
Open Scope N.

Definition bswap32 (x : N) : N :=
  (((x .& 0xff) << 24) .| (((x >> 8) .& 0xff) << 16)) .|
  (((x >> 16) .& 0xff) << 8) .| ((x >> 24) .& 0xff).

Lemma bswap32_low_byte (x : N) :
  (x mod 2^8) << 24 = (x << 24) mod 2^32.
Proof.
  rewrite !N.shiftl_mul_pow2.
  change (2^32) with (2^8 * 2^24).
  rewrite N.Div0.mul_mod_distr_r by discriminate.
  reflexivity.
Qed.

Definition bswap16 (x : N) : N :=
  ((x .& 0xff) << 8) .| ((x >> 8) .& 0xff).

Definition rev16_32 (x : N) : N :=
  ((((x >> 16) .& 0xff) << 24) .| (((x >> 24) .& 0xff) << 16)) .|
  ((x .& 0xff) << 8) .| ((x >> 8) .& 0xff).

Lemma bswap16_low_byte (x : N) :
  (x << 8) mod 2^16 = (x mod 2^8) << 8.
Proof.
  rewrite !N.shiftl_mul_pow2.
  change (2^16) with (2^8 * 2^8).
  rewrite N.Div0.mul_mod_distr_r by discriminate.
  reflexivity.
Qed.

Lemma bswap16_shifted (x : N) :
  ((x << 8) .| ((x >> 8) mod 2^8)) mod 2^16 = bswap16 x.
Proof.
  unfold bswap16. psimpl.
  rewrite <- !N.land_ones. rewrite !N.land_lor_distr_l.
  rewrite <- N.land_assoc.
  replace (N.ones 8 .& N.ones 16) with (N.ones 8) by reflexivity.
  rewrite !N.land_ones. rewrite bswap16_low_byte. reflexivity.
Qed.

Lemma rev16_32_low (x : N) :
  (rev16_32 x) mod 2^16 = bswap16 x.
Proof.
  unfold rev16_32. psimpl. apply bswap16_shifted.
Qed.

Ltac solve_range_movhi x limit mid frame :=
  destruct (N.lt_trichotomy x limit) as [LT|[EQ|GT]];
  [ assert (HLE : (x <=? limit) = true) by (apply N.leb_le; lia);
    assert (HCF : (limit <=? x) = false) by (apply N.leb_gt; exact LT);
    assert (HZF : (x =? limit) = false) by (apply N.eqb_neq; lia);
    rewrite HCF, HZF in *;
    arm7_step;
    unfold mid, frame; rewrite HLE, HCF, HZF;
    elimstore; repeat split; psimpl; try assumption; try reflexivity; try lia
  | assert (HLE : (x <=? limit) = true) by (apply N.leb_le; lia);
    assert (HCF : (limit <=? x) = true) by (apply N.leb_le; lia);
    assert (HZF : (x =? limit) = true) by (apply N.eqb_eq; exact EQ);
    rewrite HCF, HZF in *;
    arm7_step;
    unfold mid, frame; rewrite HLE, HCF, HZF;
    elimstore; repeat split; psimpl; try assumption; try reflexivity; try lia
  | assert (HLE : (x <=? limit) = false) by (apply N.leb_gt; exact GT);
    assert (HCF : (limit <=? x) = true) by (apply N.leb_le; lia);
    assert (HZF : (x =? limit) = false) by (apply N.eqb_neq; lia);
    rewrite HCF, HZF in *;
    arm7_step;
    unfold mid, frame; rewrite HLE, HCF, HZF;
    elimstore; repeat split; psimpl; try assumption; try reflexivity; try lia ].

Lemma msub_eqb_spec (x y z : N) (HYZ : y <= z) (HZ : z < 2^32) :
  ((x ⊖ y) =? (z-y)) = (x mod 2^32 =? z).
Proof.
  destruct (x mod 2^32 =? z) eqn:E.
  - apply N.eqb_eq in E. apply N.eqb_eq.
    rewrite <- (msub_mod_l 32 32 x y) by reflexivity.
    rewrite E, msub_sub by exact HYZ.
    rewrite N.mod_small by lia. reflexivity.
  - apply N.eqb_neq in E. apply N.eqb_neq. intro EQ.
    pose proof (msub_add 32 x y) as Hadd.
    rewrite EQ, N.sub_add in Hadd by exact HYZ.
    rewrite N.mod_small in Hadd by exact HZ.
    apply E. symmetry. exact Hadd.
Qed.
