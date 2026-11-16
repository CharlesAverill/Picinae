(* Grok Bot (agent coqettu): two's-complement quotient/remainder lemmas for sdiv/msub sequences. *)
From Stdlib Require Import Utf8 NArith ZArith Lia Bool.
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

Lemma toZ64_range: ∀ n, (-2^63 <= toZ (64:N) n < 2^63)%Z.
Proof.
  intros. unfold toZ, canonicalZ. change (Z.pred (Z.of_N 64)) with 63%Z. change (Z.of_N 64) with 64%Z.
  pose proof (Z.mod_pos_bound (Z.of_N n + 2^63) (2^64) ltac:(lia)). lia.
Qed.

(* Quotient as computed by the lifted sdiv (zero divisor yields 0) and remainder as msub. *)
Definition sdiv64 (a b:N) : N := if b =? 0 then 0 else sbop2 Z.quot 64 a b.
Definition srem64 (a b:N) : N := msub 64 a (sdiv64 a b * b).

Theorem sdiv64_srem64_semantics:
  ∀ a b, toZ (64:N) b ≠ 0%Z -> ~ (toZ (64:N) a = -2^63 /\ toZ (64:N) b = -1)%Z ->
  toZ (64:N) (sdiv64 a b) = Z.quot (toZ (64:N) a) (toZ (64:N) b) /\
  toZ (64:N) (srem64 a b) = Z.rem (toZ (64:N) a) (toZ (64:N) b).
Proof.
  intros a b NZ NO.
  assert (QQ: toZ (64:N) (sdiv64 a b) = Z.quot (toZ (64:N) a) (toZ (64:N) b)).
  { unfold sdiv64. destruct (N.eqb_spec b 0) as [E|E]. { subst b. exfalso. apply NZ. reflexivity. }
    unfold sbop2. rewrite toZ_ofZ_canonicalZ by lia. change (Z.of_N 64) with 64%Z.
    apply canon64_id, quot_range; [apply toZ64_range | exact NZ | exact NO]. }
  split. exact QQ.
  unfold srem64. rewrite toZ_msub, toZ_mul. change (Z.of_N 64) with 64%Z.
  rewrite canon64_sub_canon, QQ, (Z.mul_comm (Z.quot _ _)), <- (Z.rem_eq _ _ NZ).
  apply canon64_id, rem_range; [apply toZ64_range | exact NZ].
Qed.

(* bfi xd, xn, #32, #32 as psimpl leaves it *)
Lemma shl32_hi_mask: ∀ x, N.land (N.shiftl x 32) 18446744069414584320 = N.shiftl (x mod 2^32) 32.
Proof.
  intro x. change 18446744069414584320 with (N.shiftl (N.ones 32) 32).
  apply N.bits_inj. intro i. rewrite N.land_spec.
  destruct (N.lt_ge_cases i 32) as [L|G].
  - rewrite !N.shiftl_spec_low by assumption. reflexivity.
  - rewrite !N.shiftl_spec_high' by assumption.
    destruct (N.lt_ge_cases (i-32) 32) as [L2|G2].
    + rewrite N.ones_spec_low, N.mod_pow2_bits_low by assumption. apply andb_true_r.
    + rewrite N.ones_spec_high, N.mod_pow2_bits_high by assumption. apply andb_false_r.
Qed.

(* 32-bit div as the machine computes it (sdiv w gives 0 for a zero divisor) *)
Definition sdiv32 (a b:N) : N :=
  if b mod 2^32 =? 0 then 0 else sbop2 Z.quot 32 (a mod 2^32) (b mod 2^32) mod 2^32.
Definition srem32 (a b:N) : N :=
  if b mod 2^32 =? 0 then a mod 2^32
  else msub 32 a (sbop2 Z.quot 32 (a mod 2^32) (b mod 2^32) * b).

Lemma canon32_id: ∀ z, (-2^31 <= z < 2^31)%Z -> canonicalZ 32 z = z.
Proof. intros z H. unfold canonicalZ. change (Z.pred 32) with 31%Z. rewrite Z.mod_small by lia. lia. Qed.

Lemma canon32_sub_canon: ∀ a x, canonicalZ 32 (a - canonicalZ 32 x) = canonicalZ 32 (a - x).
Proof.
  intros. unfold canonicalZ. change (Z.pred 32) with 31%Z. f_equal.
  rewrite (Z.mod_eq (x + 2^31)) by lia.
  replace (a - ((x + 2 ^ 31) - 2^32 * ((x + 2 ^ 31) / 2^32) - 2 ^ 31) + 2 ^ 31)%Z
    with ((a - x + 2^31) + ((x + 2 ^ 31) / 2^32) * 2^32)%Z by ring.
  apply Z.mod_add. lia.
Qed.

Lemma quot_range32: ∀ A B, (-2^31 <= A < 2^31)%Z -> B ≠ 0%Z -> ~ (A = -2^31 /\ B = -1)%Z ->
  (-2^31 <= Z.quot A B < 2^31)%Z.
Proof.
  intros A B HA HB HO.
  pose proof (Z.quot_abs A B HB) as QA.
  rewrite Z.quot_div_nonneg in QA by lia.
  pose proof (Z.div_mod (Z.abs A) (Z.abs B) ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (Z.abs A) (Z.abs B) ltac:(lia)) as MB.
  assert (Q0: (0 <= Z.abs A / Z.abs B)%Z) by (apply Z.div_pos; lia).
  assert (QL: (Z.abs A / Z.abs B <= Z.abs A)%Z) by nia.
  destruct (Z.eq_dec (Z.abs A / Z.abs B) (2^31)) as [E|E].
  - assert (Z.abs B = 1)%Z by nia. assert (Z.abs A = 2^31)%Z by lia.
    assert (A = -2^31)%Z by lia.
    destruct (Z.eq_dec B 1); [subst; rewrite Z.quot_1_r; lia|].
    exfalso. apply HO. split; lia.
  - lia.
Qed.

Lemma toZ32_range: ∀ n, (-2^31 <= toZ (32:N) n < 2^31)%Z.
Proof.
  intros. unfold toZ, canonicalZ. change (Z.pred (Z.of_N 32)) with 31%Z. change (Z.of_N 32) with 32%Z.
  pose proof (Z.mod_pos_bound (Z.of_N n + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma toZ32_quot: ∀ a b, toZ (32:N) b ≠ 0%Z -> ~ (toZ (32:N) a = -2^31 /\ toZ (32:N) b = -1)%Z ->
  toZ 32 (sbop2 Z.quot 32 (a mod 2^32) (b mod 2^32)) = Z.quot (toZ 32 a) (toZ 32 b).
Proof.
  intros a b NZ NO. unfold sbop2. rewrite !(toZ_mod_pow2 32 32) by reflexivity.
  rewrite toZ_ofZ_canonicalZ by reflexivity. change (Z.of_N 32) with 32%Z.
  apply canon32_id, quot_range32; [apply toZ32_range | exact NZ | exact NO].
Qed.

Theorem sdiv32_srem32_semantics:
  ∀ a b, toZ (32:N) b ≠ 0%Z -> ~ (toZ (32:N) a = -2^31 /\ toZ (32:N) b = -1)%Z ->
  toZ 32 (sdiv32 a b) = Z.quot (toZ 32 a) (toZ 32 b) /\
  toZ 32 (srem32 a b) = Z.rem (toZ 32 a) (toZ 32 b).
Proof.
  intros a b NZ NO.
  assert (BZ: (b mod 2^32 =? 0) = false).
  { apply N.eqb_neq. intro E. apply NZ. rewrite <- (toZ_mod_pow2 32 32) by reflexivity. rewrite E. reflexivity. }
  unfold sdiv32, srem32. rewrite BZ. split.
  - rewrite (toZ_mod_pow2 32 32) by reflexivity. apply toZ32_quot; assumption.
  - rewrite toZ_msub, toZ_mul. change (Z.of_N 32) with 32%Z.
    rewrite canon32_sub_canon, toZ32_quot by assumption.
    rewrite (Z.mul_comm (Z.quot _ _)), <- (Z.rem_eq _ _ NZ).
    apply canon32_id. pose proof (Z.rem_bound_abs (toZ 32 a) (toZ 32 b) NZ).
    pose proof (toZ32_range b). lia.
Qed.
