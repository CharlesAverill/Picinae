(* Signed CMP/JG/CMOVG facts for the wrapper's bounded limb counts. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
From Stdlib Require Import NArith ZArith Lia Bool.
Import X64Notations.
Open Scope N.
Lemma toZ_nonnegative64 : forall x, x<2^63 -> toZ 64 x=Z.of_N x.
Proof.
  intros x B. pose proof (proj1 (toZ_nonneg 64 x) ltac:(rewrite N.mod_small by lia; exact B)) as EQ.
  rewrite N.mod_small in EQ by lia. exact EQ.
Qed.
Lemma slt_msub_positive64 : forall x y,
  x<2^63 -> y<2^63 -> slt 64 (x ⊖ y) 0=(x <? y).
Proof.
  intros x y X Y. unfold slt. rewrite toZ_0_r,toZ_msub.
  rewrite (toZ_nonnegative64 x X),(toZ_nonnegative64 y Y).
  rewrite canonicalZ_id with (w':=64) by (unfold signed_range; cbn; lia).
  destruct (x <? y) eqn:E; [apply N.ltb_lt in E; apply Z.ltb_lt | apply N.ltb_ge in E; apply Z.ltb_ge]; lia.
Qed.
Lemma sign_shift64 : forall x,
  x<2^64 -> x >> 63=0 \/ x >> 63=1.
Proof. intros x B. rewrite N.shiftr_div_pow2. assert (x/2^63<2) by (apply N.Div0.div_lt_upper_bound; lia). lia. Qed.
Definition cmp_of64 x y := ((x >> 63 .^ (x ⊖ y) >> 63) .& ((x ⊖ y) >> 63 .^ y >> 63 .^ 1)) mod 2.
Lemma cmp_of_positive64 : forall x y,
  x<2^63 -> y<2^63 -> cmp_of64 x y=0.
Proof.
  intros x y X Y.
  assert (SX:x >> 63=0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact X).
  assert (SY:y >> 63=0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact Y).
  destruct (sign_shift64 (x ⊖ y) (ltac:(apply mp2_mod_lt))) as [D|D];
    unfold cmp_of64; rewrite SX,SY,D; reflexivity.
Qed.
Definition cmp_gt64 x y :=
  if cmp_of64 x y =? (if slt 64 (x ⊖ y) 0 then 1 else 0)
    then if x mod 2^64 =? y mod 2^64 then 0 else 1 else 0.
Lemma cmp_gt_positive64 : forall x y,
  x<2^63 -> y<2^63 -> cmp_gt64 x y=(if y <? x then 1 else 0).
Proof.
  intros x y X Y. unfold cmp_gt64. rewrite cmp_of_positive64,slt_msub_positive64 by assumption.
  rewrite !N.mod_small by lia.
  destruct (x <? y) eqn:XY, (y <? x) eqn:YX, (x =? y) eqn:EQ;
    try reflexivity; apply N.ltb_lt in XY || apply N.ltb_ge in XY;
    apply N.ltb_lt in YX || apply N.ltb_ge in YX;
    apply N.eqb_eq in EQ || apply N.eqb_neq in EQ; lia.
Qed.


Definition cmp_of_raw64 x y :=
  (x >> 63 .^ (x ⊖ y) >> 63) .& ((x ⊖ y) >> 63 .^ y >> 63 .^ 1).
Lemma cmp_of_raw_positive64 : forall x y,
  x<2^63 -> y<2^63 -> cmp_of_raw64 x y=0.
Proof.
  intros x y X Y.
  assert (SX:x >> 63=0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact X).
  assert (SY:y >> 63=0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact Y).
  destruct (sign_shift64 (x ⊖ y) (ltac:(apply mp2_mod_lt))) as [D|D];
    unfold cmp_of_raw64; rewrite SX,SY,D; reflexivity.
Qed.
Lemma cmp_gt_raw_positive64 : forall x y,
  x<2^63 -> y<2^63 ->
  (if cmp_of_raw64 x y =? (if slt 64 (x ⊖ y) 0 then 1 else 0)
    then if x =? y then 0 else 1 else 0)=(if y <? x then 1 else 0).
Proof.
  intros x y X Y. rewrite cmp_of_raw_positive64,slt_msub_positive64 by assumption.
  destruct (x <? y) eqn:XY, (y <? x) eqn:YX, (x =? y) eqn:EQ;
    try reflexivity; apply N.ltb_lt in XY || apply N.ltb_ge in XY;
    apply N.ltb_lt in YX || apply N.ltb_ge in YX;
    apply N.eqb_eq in EQ || apply N.eqb_neq in EQ; lia.
Qed.

Definition machine_chunk_count n k :=
  let remaining := n ⊖ k in
  if N.lnot (if cmp_of_raw64 remaining 170 =? (if slt 64 (remaining ⊖ 170) 0 then 1 else 0)
       then if remaining =? 170 then 0 else 1 else 0) 1 =? 0
    then 170 else remaining.
Lemma wrapper_machine_chunk_count : forall n k,
  n+170<2^63 -> k<n -> machine_chunk_count n k=chunk_size n k.
Proof.
  intros n k N K. unfold machine_chunk_count.
  rewrite msub_sub by lia. rewrite N.mod_small by lia.
  rewrite cmp_gt_raw_positive64 by lia.
  unfold chunk_size. destruct (170 <? n-k) eqn:C.
  - apply N.ltb_lt in C. rewrite N.min_l by lia. reflexivity.
  - apply N.ltb_ge in C. rewrite N.min_r by lia. reflexivity.
Qed.

Lemma msub_eqb_add64 : forall x y z,
  x<2^64 -> (x ⊖ y =? z mod 2^64)=(x =? (y+z) mod 2^64).
Proof.
  intros x y z B. apply eq_true_iff_eq. rewrite !N.eqb_eq. split; intro E.
  - apply (f_equal (fun a => (a+y) mod 2^64)) in E.
    rewrite msub_add,N.Div0.add_mod_idemp_l in E.
    rewrite N.mod_small in E by exact B. rewrite N.add_comm in E. exact E.
  - rewrite E,msub_mod_l,add_msub_l by reflexivity. reflexivity.
Qed.
