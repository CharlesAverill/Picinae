From Stdlib Require Import Utf8 NArith ZArith Lia.
Require Import Picinae_armv8.
Open Scope N.
Lemma ashiftr2_shl2: ∀ x, x < 2^64 -> x mod 4 = 0 -> ((ashiftr 64 x 2) << 2) mod 2^64 = x.
Proof.
  intros x X M. unfold ashiftr, sbop1. set (z := toZ 64 x).
  assert (E: ofZ 64 z = x) by (unfold z; rewrite ofZ_toZ_bitcast by reflexivity; apply N.mod_small; exact X).
  unfold ofZ in *. rewrite N.shiftl_mul_pow2.
  apply N2Z.inj. rewrite N2Z.inj_mod, N2Z.inj_mul, Z2N.id by (apply Z.mod_pos_bound; lia).
  rewrite <- E. rewrite Z2N.id by (apply Z.mod_pos_bound; lia).
  change (Z.of_N (2^64)) with (2^64)%Z. change (Z.of_N (2^2)) with 4%Z.
  change (2^Z.of_N 64)%Z with (2^64)%Z. change (Z.of_N 2) with 2%Z.
  rewrite Z.shiftr_div_pow2 by lia. change (2^2)%Z with 4%Z.
  rewrite Z.mul_mod_idemp_l by lia.
  assert (Z4: (z mod 4 = 0)%Z).
  { apply (f_equal Z.of_N) in E. rewrite Z2N.id in E by (apply Z.mod_pos_bound; lia).
    assert (MZ: (Z.of_N x mod 4 = 0)%Z) by (change 4%Z with (Z.of_N 4); rewrite <- N2Z.inj_mod, M; reflexivity).
    apply (f_equal (fun a => a mod 4)%Z) in E. rewrite MZ in E.
    rewrite <- (Z.mod_mod_divide z (2^64) 4) by (exists (2^62)%Z; reflexivity). lia. }
  f_equal. rewrite Z.mul_comm. symmetry. apply Z.div_exact. lia. exact Z4.
Qed.
