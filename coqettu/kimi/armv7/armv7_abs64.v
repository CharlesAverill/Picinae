From Stdlib Require Import NArith.
Require Import Picinae_armv7.
Import ARM7Notations.
Open Scope N.

Definition signmask32 (x : N) : N := if slt 32 x 0 then N.ones 32 else 0.

Lemma ashiftr31_signmask x : ashiftr 32 x 31 = signmask32 x.
Proof.
  unfold signmask32, slt. rewrite toZ_0_r, <- signbit by discriminate.
  change (N.pred 32) with 31. apply N.bits_inj. intro i.
  rewrite ashiftr_spec. destruct (N.ltb_spec i 32).
  - replace (N.min (i+31) (N.pred 32)) with 31 by lia.
    cbn [andb]. destruct (N.testbit x 31).
    + symmetry. apply N.ones_spec_low. lia.
    + symmetry. apply N.bits_0.
  - cbn [andb]. destruct (N.testbit x 31).
    + symmetry. apply N.ones_spec_high. lia.
    + symmetry. apply N.bits_0.
Qed.

Definition abs64_low (hi lo : N) : N :=
  if slt 32 hi 0 then 0 ⊖ lo else lo.

Definition abs64_high (hi lo : N) : N :=
  if slt 32 hi 0 then (0 ⊖ hi) ⊖ (if lo =? 0 then 0 else 1) else hi.

Lemma lxor_ones_msub_ones (x : N) (H : x < 2^32) :
  (N.lxor x (N.ones 32)) ⊖ (N.ones 32) = 0 ⊖ x.
Proof.
  change (N.lxor x (N.ones 32)) with (N.lnot x 32).
  rewrite lnot_sub_low2 by exact H.
  unfold msub.
  replace (N.ones 32 mod 2^32) with (N.ones 32) by reflexivity.
  replace (x mod 2^32) with x by (symmetry; apply N.mod_small; exact H).
  change (N.ones 32) with (2^32-1).
  replace (2^32-1-x + (2^32-(2^32-1))) with (2^32-x) by lia.
  reflexivity.
Qed.

Lemma ones_le_lxor_ones (x : N) (H : x < 2^32) :
  (N.ones 32 <=? N.lxor x (N.ones 32)) = (x =? 0).
Proof.
  change (N.lxor x (N.ones 32)) with (N.lnot x 32).
  rewrite lnot_sub_low2 by exact H.
  change (N.ones 32) with (2^32-1).
  destruct x.
  - reflexivity.
  - replace (N.pos p =? 0) with false by reflexivity.
    apply N.leb_gt. lia.
Qed.

Lemma abs64_low_mask (hi lo : N) (HLO : lo < 2^32) :
  (N.lxor lo (signmask32 hi)) ⊖ (signmask32 hi) = abs64_low hi lo.
Proof.
  unfold signmask32, abs64_low. destruct (slt 32 hi 0).
  - apply lxor_ones_msub_ones. exact HLO.
  - rewrite N.lxor_0_r, msub_0_r, N.mod_small by exact HLO. reflexivity.
Qed.

Lemma abs64_high_mask (hi lo : N) (HHI : hi < 2^32) (HLO : lo < 2^32) :
  ((N.lxor hi (signmask32 hi)) ⊖ (signmask32 hi)) ⊖
    (if signmask32 hi <=? N.lxor lo (signmask32 hi) then 0 else 1) =
  abs64_high hi lo.
Proof.
  unfold signmask32, abs64_high. destruct (slt 32 hi 0).
  - rewrite lxor_ones_msub_ones by exact HHI.
    rewrite ones_le_lxor_ones by exact HLO. reflexivity.
  - rewrite !N.lxor_0_r, !msub_0_r, !N.mod_small by assumption.
    replace (0 <=? lo) with true by (symmetry; apply N.leb_le; lia).
    rewrite msub_0_r, N.mod_small by exact HHI. reflexivity.
Qed.
