Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import amd64_common.
Open Scope N.

(* Lemmas for the IEEE-754 classification functions (isnan, finite, ...).
   glibc tests a float's bits with integer arithmetic: (c - a) >> (w-1) is
   the borrow of c - a.  Written by Claude Opus 5.5 (claude-opus-5-5) and
   checked by Rocq. *)

(* Fields of a binary64 / binary32 bit pattern b. *)
Definition exp64 (b:N) := (b >> 52) mod 2^11.
Definition man64 (b:N) := b mod 2^52.
Definition exp32 (b:N) := (b >> 23) mod 2^8.
Definition man32 (b:N) := b mod 2^23.

(* NaN: exponent all ones, mantissa nonzero.  Infinite or NaN: exponent all
   ones. *)
Definition is_nan64 b := (exp64 b =? 2047) && negb (man64 b =? 0).
Definition is_nan32 b := (exp32 b =? 255) && negb (man32 b =? 0).
Definition is_finite64 b := negb (exp64 b =? 2047).
Definition is_finite32 b := negb (exp32 b =? 255).

Lemma shr_msub64: forall c a, c < 2^63 -> a < 2^63 -> msub 64 c a >> 63 = if c <? a then 1 else 0.
Proof.
  intros c a C A. rewrite N.shiftr_div_pow2.
  change (2^63) with 9223372036854775808 in *.
  destruct (N.ltb_spec c a) as [H|H].
  - rewrite msub_wrap by (rewrite !N.mod_small; change (2^64) with 18446744073709551616; lia).
    rewrite !N.mod_small by (change (2^64) with 18446744073709551616; lia).
    change (2^64) with 18446744073709551616.
    symmetry. apply N.div_unique with (r := 18446744073709551616 + c - a - 9223372036854775808); lia.
  - rewrite msub_nowrap by (rewrite !N.mod_small; change (2^64) with 18446744073709551616; lia).
    rewrite !N.mod_small by (change (2^64) with 18446744073709551616; lia).
    apply N.div_small. lia.
Qed.

Lemma shr_msub32: forall c a, c < 2^31 -> a < 2^31 -> msub 32 c a >> 31 = if c <? a then 1 else 0.
Proof.
  intros c a C A. rewrite N.shiftr_div_pow2.
  change (2^31) with 2147483648 in *.
  destruct (N.ltb_spec c a) as [H|H].
  - rewrite msub_wrap by (rewrite !N.mod_small; change (2^32) with 4294967296; lia).
    rewrite !N.mod_small by (change (2^32) with 4294967296; lia).
    change (2^32) with 4294967296.
    symmetry. apply N.div_unique with (r := 4294967296 + c - a - 2147483648); lia.
  - rewrite msub_nowrap by (rewrite !N.mod_small; change (2^32) with 4294967296; lia).
    rewrite !N.mod_small by (change (2^32) with 4294967296; lia).
    apply N.div_small. lia.
Qed.

(* |b| > +inf's pattern exactly for NaNs. *)
Lemma nan64_iff: forall b, (0x7ff0000000000000 <? b mod 2^63) = is_nan64 b.
Proof.
  intro b. unfold is_nan64, exp64, man64. rewrite N.shiftr_div_pow2.
  assert (E: b mod 2^63 = (b / 2^52) mod 2^11 * 2^52 + b mod 2^52).
  { rewrite (N.div_mod b (2^52)) at 1 by discriminate.
    change (2^63) with (2^52 * 2^11). rewrite N.mul_comm.
    rewrite N.mod_mul_r by discriminate. lia. }
  rewrite E. pose proof (N.mod_lt (b / 2^52) (2^11) ltac:(discriminate)).
  pose proof (N.mod_lt b (2^52) ltac:(discriminate)).
  change (2^11) with 2048 in *. change (2^52) with 4503599627370496 in *.
  destruct (N.eqb_spec ((b / 4503599627370496) mod 2048) 2047);
  destruct (N.eqb_spec (b mod 4503599627370496) 0); cbn [andb negb];
  [apply N.ltb_ge | apply N.ltb_lt | apply N.ltb_ge | apply N.ltb_ge]; lia.
Qed.

Lemma nan32_iff: forall b, (0x7f800000 <? b mod 2^31) = is_nan32 b.
Proof.
  intro b. unfold is_nan32, exp32, man32. rewrite N.shiftr_div_pow2.
  assert (E: b mod 2^31 = (b / 2^23) mod 2^8 * 2^23 + b mod 2^23).
  { rewrite (N.div_mod b (2^23)) at 1 by discriminate.
    change (2^31) with (2^23 * 2^8). rewrite N.mul_comm.
    rewrite N.mod_mul_r by discriminate. lia. }
  rewrite E. pose proof (N.mod_lt (b / 2^23) (2^8) ltac:(discriminate)).
  pose proof (N.mod_lt b (2^23) ltac:(discriminate)).
  change (2^8) with 256 in *. change (2^23) with 8388608 in *.
  destruct (N.eqb_spec ((b / 8388608) mod 256) 255);
  destruct (N.eqb_spec (b mod 8388608) 0); cbn [andb negb];
  [apply N.ltb_ge | apply N.ltb_lt | apply N.ltb_ge | apply N.ltb_ge]; lia.
Qed.

(* b .& exponent-mask is below the mask exactly for finite values. *)
Lemma finite64_iff: forall b, (b .& 0x7ff0000000000000 <? 0x7ff0000000000000) = is_finite64 b.
Proof.
  intro b. unfold is_finite64, exp64.
  replace (b .& 0x7ff0000000000000) with (((b >> 52) mod 2^11) * 2^52).
  - pose proof (N.mod_lt (b >> 52) (2^11) ltac:(discriminate)). change (2^11) with 2048 in *.
    destruct (N.eqb_spec ((b >> 52) mod 2048) 2047); cbn [negb];
    [apply N.ltb_ge | apply N.ltb_lt]; change (2^52) with 4503599627370496; lia.
  - rewrite <- N.shiftl_mul_pow2. apply N.bits_inj. intro i. rewrite N.land_spec.
    destruct (N.ltb_spec i 52).
    + rewrite N.shiftl_spec_low by lia.
      change 0x7ff0000000000000 with (N.shiftl (N.ones 11) 52). rewrite N.shiftl_spec_low by lia.
      symmetry. apply Bool.andb_false_r.
    + rewrite N.shiftl_spec_high by lia.
      change 0x7ff0000000000000 with (N.shiftl (N.ones 11) 52). rewrite N.shiftl_spec_high by lia.
      destruct (N.ltb_spec (i - 52) 11).
      * rewrite N.mod_pow2_bits_low, N.shiftr_spec by lia. replace (i - 52 + 52) with i by lia.
        rewrite N.ones_spec_low by lia. rewrite Bool.andb_true_r. reflexivity.
      * rewrite N.mod_pow2_bits_high by lia.
        rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma finite32_iff: forall b, (b .& 0x7f800000 <? 0x7f800000) = is_finite32 b.
Proof.
  intro b. unfold is_finite32, exp32.
  replace (b .& 0x7f800000) with (((b >> 23) mod 2^8) * 2^23).
  - pose proof (N.mod_lt (b >> 23) (2^8) ltac:(discriminate)). change (2^8) with 256 in *.
    destruct (N.eqb_spec ((b >> 23) mod 256) 255); cbn [negb];
    [apply N.ltb_ge | apply N.ltb_lt]; change (2^23) with 8388608; lia.
  - rewrite <- N.shiftl_mul_pow2. apply N.bits_inj. intro i. rewrite N.land_spec.
    destruct (N.ltb_spec i 23).
    + rewrite N.shiftl_spec_low by lia.
      change 0x7f800000 with (N.shiftl (N.ones 8) 23). rewrite N.shiftl_spec_low by lia.
      symmetry. apply Bool.andb_false_r.
    + rewrite N.shiftl_spec_high by lia.
      change 0x7f800000 with (N.shiftl (N.ones 8) 23). rewrite N.shiftl_spec_high by lia.
      destruct (N.ltb_spec (i - 23) 8).
      * rewrite N.mod_pow2_bits_low, N.shiftr_spec by lia. replace (i - 23 + 23) with i by lia.
        rewrite N.ones_spec_low by lia. rewrite Bool.andb_true_r. reflexivity.
      * rewrite N.mod_pow2_bits_high by lia.
        rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. reflexivity.
Qed.

(* x87 80-bit extended precision, as long double arguments arrive on the
   stack: lo = significand bits 0..31, hi = significand bits 32..63 (bit 63
   is the explicit integer bit), se = sign (bit 15) and exponent (bits 0..14). *)
Definition exp80 (se:N) := se mod 2^15.

Lemma lor_shiftl_add: forall a b k, b < 2^k -> a << k .| b = a * 2^k + b.
Proof.
  intros a b k B. rewrite <- N.shiftl_mul_pow2, <- N.lxor_lor, N.add_nocarry_lxor; [reflexivity|..];
  apply N.bits_inj; intro i; rewrite N.land_spec, N.bits_0;
  (destruct (N.ltb_spec i k);
   [rewrite N.shiftl_spec_low by lia; reflexivity
   |rewrite <- (N.mod_small b (2^k) B), N.mod_pow2_bits_high by lia; apply Bool.andb_false_r]).
Qed.

Lemma lor32: forall x y, x < 2^32 -> y < 2^32 -> x .| y < 2^32.
Proof.
  intros x y X Y. rewrite <- (N.mod_small x _ X), <- (N.mod_small y _ Y).
  change (2^32) with (2^32) at 3. rewrite <- N.land_ones, <- N.land_ones, <- N.land_lor_distr_l, N.land_ones.
  apply N.mod_lt. discriminate.
Qed.

Lemma mod16_15: forall x, (x mod 2^16) mod 2^15 = x mod 2^15.
Proof.
  intro x. apply N.bits_inj. intro i. destruct (N.ltb_spec i 15).
  - rewrite !N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma shr31_cases: forall x, x < 2^32 -> x >> 31 = if 2^31 <=? x then 1 else 0.
Proof.
  intros x X. rewrite N.shiftr_div_pow2. change (2^32) with 4294967296 in X. change (2^31) with 2147483648.
  destruct (N.leb_spec 2147483648 x); [symmetry; apply N.div_unique with (r := x - 2147483648) | apply N.div_small]; lia.
Qed.

(* finitel: x | 0xffff8000 sets bits 15..31, so 1 + that carries out exactly
   when the low 15 bits (the exponent) are all ones. *)
Lemma or_hi17: forall x, x < 2^32 -> x .| 4294934528 = 4294934528 + x mod 2^15.
Proof.
  intros x X. change 4294934528 with (N.ones 17 * 2^15). rewrite <- lor_shiftl_add by (apply N.mod_lt; discriminate).
  rewrite <- N.shiftl_mul_pow2.
  apply N.bits_inj. intro i. rewrite !N.lor_spec. destruct (N.ltb_spec i 15).
  - rewrite N.shiftl_spec_low, N.mod_pow2_bits_low by lia. apply Bool.orb_false_r.
  - rewrite N.shiftl_spec_high, N.mod_pow2_bits_high by lia. rewrite Bool.orb_false_r.
    destruct (N.ltb_spec (i - 15) 17).
    + rewrite N.ones_spec_low by lia. apply Bool.orb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.orb_false_r.
      apply N.bits_above_log2. destruct (N.eq_0_gt_0_cases x) as [->|XP]. cbn. lia.
      apply N.log2_lt_pow2 in X; [lia|exact XP].
Qed.

Lemma finitel_bits: forall x, x < 2^32 ->
  ((1 + (x .| 4294934528)) mod 2^32) >> 31 = if x mod 2^15 =? 32767 then 0 else 1.
Proof.
  intros x X. rewrite (or_hi17 x X). pose proof (N.mod_lt x (2^15) ltac:(discriminate)).
  remember (x mod 2^15) as r. clear Heqr. rewrite N.shiftr_div_pow2.
  change (2^32) with 4294967296. change (2^31) with 2147483648. change (2^15) with 32768 in *.
  destruct (N.eqb_spec r 32767).
  - subst r. reflexivity.
  - rewrite N.mod_small by lia. symmetry. apply N.div_unique with (r := 1 + (4294934528 + r) - 2147483648); lia.
Qed.

(* isnanl *)
Definition isnanl_spec (lo hi se:N) :=
  (if (exp80 se =? 0) || N.testbit hi 31 then 0 else 1) .|
  (if (exp80 se =? 0x7fff) && negb (hi mod 2^31 .| lo =? 0) then 0xffff else 0).

Lemma dbl_mask: forall w, (w + w) .& 65534 = (w mod 2^15) << 1.
Proof.
  intro w. replace (w + w) with (w << 1) by (rewrite N.shiftl_mul_pow2; lia).
  change 65534 with (N.ones 15 << 1). rewrite <- N.shiftl_land, N.land_ones. reflexivity.
Qed.

Lemma neg_or_shr31: forall f, f < 2^32 -> (msub 32 0 f .| f) >> 31 = if f =? 0 then 0 else 1.
Proof.
  intros f F. destruct (N.eqb_spec f 0) as [->|NZ]. reflexivity.
  rewrite N.shiftr_lor. assert (E: msub 32 0 f = 2^32 - f).
  { unfold msub. rewrite (N.mod_small f) by assumption. rewrite N.add_0_l, N.mod_small; lia. }
  rewrite E, !shr31_cases by lia.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648.
  destruct (N.leb_spec 2147483648 (4294967296 - f)), (N.leb_spec 2147483648 f); try lia; reflexivity.
Qed.

Lemma isnanl_bits: forall lo hi w, lo < 2^32 -> hi < 2^32 ->
  (msub 32 0 (w + w .& 65534) .& N.lnot hi 32) >> 31
  .| msub 32 65534 ((msub 32 0 (hi mod 2^31 .| lo) .| (hi mod 2^31 .| lo)) >> 31 .| w + w .& 65534) >> 16
  = isnanl_spec lo hi w.
Proof.
  intros lo hi w LO HI. unfold isnanl_spec, exp80. rewrite dbl_mask.
  assert (FB: hi mod 2^31 .| lo < 2^32).
  { apply lor32; [|exact LO]. apply N.lt_trans with (2^31). apply N.mod_lt; discriminate. reflexivity. }
  rewrite (neg_or_shr31 _ FB).
  pose proof (N.mod_lt w (2^15) ltac:(discriminate)) as EB.
  remember (w mod 2^15) as e. clear Heqe.
  remember (hi mod 2^31 .| lo) as f. clear Heqf.
  rewrite N.shiftl_mul_pow2. change (2^1) with 2.
  (* first term *)
  replace ((msub 32 0 (e * 2) .& N.lnot hi 32) >> 31) with
          (if (e =? 0) || N.testbit hi 31 then 0 else 1).
  2: { rewrite N.shiftr_land, N.lnot_sub_low.
       2: { destruct (N.eq_0_gt_0_cases hi) as [->|HP]. cbn. lia. apply N.log2_lt_pow2; assumption. }
       rewrite testbit31_ge by assumption.
       rewrite (shr31_cases (N.ones 32 - hi)) by (change (N.ones 32) with 4294967295; change (2^32) with 4294967296 in *; lia).
       destruct (N.eqb_spec e 0) as [->|NZ].
       - reflexivity.
       - rewrite shr31_cases by (apply msub_lt).
         unfold msub. change (2^32) with 4294967296 in *. change (N.ones 32) with 4294967295.
         rewrite N.add_0_l, (N.mod_small (e*2)) by lia. rewrite (N.mod_small (4294967296 - e*2)) by lia.
         change (2^31) with 2147483648.
         destruct (N.leb_spec 2147483648 (4294967296 - e*2)); [|lia].
         destruct (N.leb_spec 2147483648 hi), (N.leb_spec 2147483648 (4294967295 - hi)); try lia; reflexivity. }
  (* second term *)
  replace (msub 32 65534 ((if f =? 0 then 0 else 1) .| e * 2) >> 16) with
          (if (e =? 32767) && negb (f =? 0) then 65535 else 0).
  2: { rewrite N.lor_comm. replace (e * 2) with (e << 1) by (rewrite N.shiftl_mul_pow2; reflexivity).
       rewrite lor_shiftl_add by (destruct (f =? 0); cbn; lia).
       rewrite N.shiftr_div_pow2. unfold msub. change (2^32) with 4294967296. change (2^15) with 32768 in *.
       change (2^16) with 65536. change (2^1) with 2.
       destruct (N.eqb_spec e 32767), (N.eqb_spec f 0); cbn [andb negb];
       rewrite (N.mod_small (e * 2 + _)) by lia; try (subst e; reflexivity);
       symmetry; apply N.div_small; lia. }
  reflexivity.
Qed.

(* isinfl *)
Definition isinfl_spec (lo hi se:N) :=
  if (exp80 se =? 0x7fff) && (hi =? 2^31) && (lo =? 0) then
    (if N.testbit se 15 then 0xffffffff else 1) else 0.

Lemma lnot_mod_low: forall y k, 0 < k -> N.lnot y k mod 2^k = N.ones k - y mod 2^k.
Proof.
  intros y k K. rewrite <- N.lnot_sub_low.
  2: { destruct (N.eq_0_gt_0_cases (y mod 2^k)) as [->|P]. cbn. exact K.
       apply N.log2_lt_pow2. exact P. apply N.mod_lt, N.pow_nonzero; discriminate. }
  apply N.bits_inj. intro i. destruct (N.ltb_spec i k).
  - rewrite N.mod_pow2_bits_low, !N.lnot_spec_low, N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite N.mod_pow2_bits_high by lia. rewrite N.lnot_spec_high, N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma neg_or_bit31: forall c, c < 2^32 -> N.testbit (msub 32 0 c .| c) 31 = negb (c =? 0).
Proof.
  intros c C. destruct (N.eqb_spec c 0) as [->|NZ]. reflexivity.
  rewrite N.lor_spec, !testbit31_ge by (apply msub_lt || exact C).
  assert (E: msub 32 0 c = 2^32 - c).
  { unfold msub. rewrite (N.mod_small c) by assumption. rewrite N.add_0_l, N.mod_small; lia. }
  rewrite E. change (2^32) with 4294967296 in *. change (2^31) with 2147483648.
  destruct (N.leb_spec 2147483648 (4294967296 - c)), (N.leb_spec 2147483648 c); try lia; reflexivity.
Qed.

Lemma ashiftr31: forall v, v < 2^32 -> ashiftr 32 v 31 = if N.testbit v 31 then N.ones 32 else 0.
Proof.
  intros v V. apply N.bits_inj. intro i. rewrite ashiftr_spec.
  destruct (N.ltb_spec i 32).
  - replace (N.min (i + 31) (N.pred 32)) with 31 by lia. cbn [andb].
    destruct (N.testbit v 31). symmetry. apply N.ones_spec_low. lia. symmetry. apply N.bits_0.
  - cbn [andb]. destruct (N.testbit v 31). symmetry. apply N.ones_spec_high. lia. symmetry. apply N.bits_0.
Qed.

Lemma sign2: forall se, ashiftr 32 (scast 16 32 se mod 2^32) 14 .& 2 = if N.testbit se 15 then 2 else 0.
Proof.
  intro se. apply N.bits_inj. intro i. rewrite N.land_spec, ashiftr_spec.
  destruct (N.eqb_spec i 1) as [->|I1].
  - replace (1 <? 32) with true by reflexivity. replace (N.min (1 + 14) (N.pred 32)) with 15 by reflexivity.
    replace (N.testbit 2 1) with true by reflexivity. rewrite Bool.andb_true_r, Bool.andb_true_l.
    rewrite N.mod_pow2_bits_low by lia.
    rewrite <- (N.mod_pow2_bits_low (scast 16 32 se) 16 15), scast_low by lia.
    rewrite N.mod_pow2_bits_low by lia. destruct (N.testbit se 15); reflexivity.
  - replace (N.testbit 2 i) with false.
    rewrite Bool.andb_false_r. destruct (N.testbit se 15); symmetry; [|apply N.bits_0].
    destruct i as [|p]; [reflexivity|]. destruct p; try reflexivity. contradiction.
    destruct i as [|p]; [reflexivity|]. destruct p; try reflexivity. contradiction.
Qed.

Lemma isinfl_bits: forall lo hi q, lo < 2^32 -> hi < 2^32 ->
  N.lnot (ashiftr 32 (((msub 32 0 (N.lnot (scast 16 32 ((q >> 0) mod 2^16)) 15 mod 2^15
            .| (msub 32 hi (2^31) .| lo))
         .| (N.lnot (scast 16 32 ((q >> 0) mod 2^16)) 15 mod 2^15
             .| (msub 32 hi (2^31) .| lo))) >> 0) mod 2^32) (31 .& 31)) 32
  .& msub 32 1 (ashiftr 32 ((scast 16 32 ((q >> 0) mod 2^16) mod 2^32 >> 0) mod 2^32) (14 .& 31) .& 2)
  = isinfl_spec lo hi (q mod 2^16).
Proof.
  intros lo hi q LO HI. rewrite !N.shiftr_0_r. change (31 .& 31) with 31. change (14 .& 31) with 14.
  set (se := q mod 2^16). rewrite N.mod_mod by discriminate. rewrite sign2.
  rewrite lnot_mod_low by reflexivity. replace (scast 16 32 se mod 2^15) with (se mod 2^15).
  2: { rewrite <- (mod16_15 (scast 16 32 se)), scast_low, mod16_15 by lia. reflexivity. }
  set (C := N.ones 15 - se mod 2^15 .| (msub 32 hi (2^31) .| lo)).
  assert (CB: C < 2^32).
  { apply lor32. pose proof (N.mod_lt se (2^15) ltac:(discriminate)). change (N.ones 15) with 32767. change (2^15) with 32768 in *. change (2^32) with 4294967296. lia.
    apply lor32; [apply msub_lt | exact LO]. }
  assert (CB2: msub 32 0 C .| C < 2^32) by (apply lor32; [apply msub_lt | exact CB]).
  rewrite (N.mod_small _ _ CB2), ashiftr31 by exact CB2. rewrite (neg_or_bit31 C CB).
  assert (CZ: (C =? 0) = (exp80 se =? 0x7fff) && (hi =? 2^31) && (lo =? 0)).
  { unfold C, exp80. pose proof (N.mod_lt se (2^15) ltac:(discriminate)).
    destruct (N.eqb_spec (N.ones 15 - se mod 2^15 .| (msub 32 hi (2^31) .| lo)) 0) as [Z|Z].
    - apply N.lor_eq_0_iff in Z. destruct Z as [Z1 Z2]. apply N.lor_eq_0_iff in Z2. destruct Z2 as [Z2 Z3].
      change (N.ones 15) with 32767 in Z1.
      unfold msub in Z2. change (2^32) with 4294967296 in *.
      replace (hi =? 2^31) with true. subst lo.
      replace (se mod 2^15 =? 32767) with true. reflexivity.
      symmetry. apply N.eqb_eq. change (2^15) with 32768 in *. lia.
      symmetry. apply N.eqb_eq. change (2^31 mod 4294967296) with 2147483648 in Z2.
      change (2^31) with 2147483648. lia.
    - symmetry. apply Bool.andb_false_iff.
      destruct (N.eqb_spec lo 0) as [->|L]; [left|right; reflexivity].
      apply Bool.andb_false_iff.
      destruct (N.eqb_spec hi (2^31)) as [->|HN]; [left|right; reflexivity].
      apply N.eqb_neq. intro E. apply Z. change (2^15) with 32768 in *. rewrite E.
      unfold msub. rewrite (N.mod_small (2^31)) by reflexivity. rewrite N.mod_same by discriminate. reflexivity. }
  rewrite CZ. unfold isinfl_spec. clear CZ CB2 CB.
  destruct ((exp80 se =? 32767) && (hi =? 2 ^ 31) && (lo =? 0)), (N.testbit se 15); reflexivity.
Qed.
