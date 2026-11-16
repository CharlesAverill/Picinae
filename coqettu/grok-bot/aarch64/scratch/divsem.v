From Stdlib Require Import Utf8 NArith ZArith Lia.
Require Import Picinae_armv8.
Open Scope N.

Lemma canon64_id: ∀ z, (-2^63 <= z < 2^63)%Z -> canonicalZ 64 z = z.
Proof. intros z H. unfold canonicalZ. change (Z.pred 64) with 63%Z. rewrite Z.mod_small by lia. lia. Qed.

Lemma canon64_sub_canon: ∀ a x, canonicalZ 64 (a - canonicalZ 64 x) = canonicalZ 64 (a - x).
Proof.
  intros. unfold canonicalZ. change (Z.pred 64) with 63%Z. f_equal.
  rewrite (Z.mod_eq (x + 2^63)) by lia.
  replace (a - ((x + 2 ^ 63) - 2^64 * ((x + 2 ^ 63) / 2^64) - 2 ^ 63) + 2 ^ 63)%Z
    with ((a - x + 2^63) + ((x + 2 ^ 63) / 2^64) * 2^64)%Z by ring.
  apply Z.mod_add. lia.
Qed.

Lemma quot_range: ∀ A B, (-2^63 <= A < 2^63)%Z -> B ≠ 0%Z -> ~ (A = -2^63 /\ B = -1)%Z ->
  (-2^63 <= Z.quot A B < 2^63)%Z.
Proof.
  intros A B HA HB HO.
  pose proof (Z.quot_abs A B HB) as QA.
  rewrite Z.quot_div_nonneg in QA by lia.
  pose proof (Z.div_mod (Z.abs A) (Z.abs B) ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (Z.abs A) (Z.abs B) ltac:(lia)) as MB.
  assert (Q0: (0 <= Z.abs A / Z.abs B)%Z) by (apply Z.div_pos; lia).
  assert (QL: (Z.abs A / Z.abs B <= Z.abs A)%Z) by nia.
  destruct (Z.eq_dec (Z.abs A / Z.abs B) (2^63)) as [E|E].
  - assert (Z.abs B = 1)%Z by nia. assert (Z.abs A = 2^63)%Z by lia.
    assert (A = -2^63)%Z by lia.
    destruct (Z.eq_dec B 1); [subst; rewrite Z.quot_1_r; lia|].
    exfalso. apply HO. split; lia.
  - lia.
Qed.

Lemma rem_range: ∀ A B, (-2^63 <= B < 2^63)%Z -> B ≠ 0%Z -> (-2^63 <= Z.rem A B < 2^63)%Z.
Proof.
  intros A B HB H0. pose proof (Z.rem_bound_abs A B H0). lia.
Qed.
