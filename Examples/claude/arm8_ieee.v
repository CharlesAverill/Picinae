Require Import Picinae_armv8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import arm8_common.
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



(* |b| > +inf's pattern exactly for NaNs. *)


(* b .& exponent-mask is below the mask exactly for finite values. *)


(* x87 80-bit extended precision, as long double arguments arrive on the
   stack: lo = significand bits 0..31, hi = significand bits 32..63 (bit 63
   is the explicit integer bit), se = sign (bit 15) and exponent (bits 0..14). *)
Definition exp80 (se:N) := se mod 2^15.





(* finitel: x | 0xffff8000 sets bits 15..31, so 1 + that carries out exactly
   when the low 15 bits (the exponent) are all ones. *)


(* isnanl *)
Definition isnanl_spec (lo hi se:N) :=
  (if (exp80 se =? 0) || N.testbit hi 31 then 0 else 1) .|
  (if (exp80 se =? 0x7fff) && negb (hi mod 2^31 .| lo =? 0) then 0xffff else 0).




(* isinfl *)
Definition isinfl_spec (lo hi se:N) :=
  if (exp80 se =? 0x7fff) && (hi =? 2^31) && (lo =? 0) then
    (if N.testbit se 15 then 0xffffffff else 1) else 0.





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
