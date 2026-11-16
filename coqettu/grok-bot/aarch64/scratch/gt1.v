From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Lemma shr63: ∀ y, y < 2^64 -> y >> 63 = (if y <? 2^63 then 0 else 1).
Proof.
  intros y Y. rewrite N.shiftr_div_pow2. destruct (N.ltb_spec y (2^63)).
  - apply N.div_small. assumption.
  - symmetry. apply N.div_unique with (r := y - 2^63); lia.
Qed.

Lemma toZ64: ∀ y, y < 2^64 -> toZ 64 y = if y <? 2^63 then Z.of_N y else (Z.of_N y - 2^64)%Z.
Proof.
  intros y Y. destruct (N.ltb_spec y (2^63)).
  - rewrite (proj1 (toZ_nonneg 64 y)); rewrite N.mod_small; first [reflexivity | assumption | (cbn; lia)].
  - rewrite (proj1 (toZ_neg 64 y)); rewrite N.mod_small; first [reflexivity | assumption | (cbn; lia)].
Qed.

Lemma msub64_1: ∀ x, 0 < x -> x < 2^64 -> msub 64 x 1 = x - 1.
Proof.
  intros x X0 X. unfold msub. rewrite (N.mod_small 1) by reflexivity.
  replace (x + (2^64 - 1)) with ((x - 1) + 1 * 2^64) by lia.
  rewrite N.Div0.mod_add. apply N.mod_small. lia.
Qed.

(* The aarch64 "gt" condition (Z=0 and N=V) after cmp x,#1, as psimpl
   leaves it: it is 0 exactly when x <= 1 as a signed 64-bit integer. *)
Lemma gt1_test: ∀ x, x < 2^64 ->
  ((if (if slt 64 (x ⊖ 1) 0 then 1 else 0) =?
       N.land (N.lxor (x >> 63) (x ⊖ 1 >> 63)) (N.lxor (x ⊖ 1 >> 63) 1)
    then if x =? 1 then 0 else 1 else 0) = 0 <-> Z.le (toZ 64 x) 1).
Proof.
  intros x X. unfold slt.
  replace (toZ 64 0) with 0%Z by reflexivity.
  destruct (N.eq_dec x 0) as [Z0|NZ].
  - subst x. vm_compute. split; intros; first [ discriminate | reflexivity | assumption ].
  - rewrite msub64_1 by lia.
    rewrite (shr63 x), (shr63 (x-1)), (toZ64 x), (toZ64 (x-1)) by lia.
    repeat match goal with
    | |- context [N.ltb ?a ?b] => destruct (N.ltb_spec a b)
    | |- context [N.eqb x 1] => destruct (N.eqb_spec x 1)
    | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
    end; cbn -[N.pow Z.pow]; try (exfalso; lia).
    all: split; intro HH; first [ discriminate | lia | reflexivity ].
Qed.
