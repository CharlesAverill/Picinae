From Stdlib Require Import Utf8 NArith Lia Bool.
Open Scope N.

Definition byte (x k : N) : N := N.shiftr x (8*k) mod 2^8.
Fixpoint Ln (n:nat) : N := match n with O => 0 | S n => Ln n + 2^(8*N.of_nat n) end.

Lemma mod_split8: ∀ x k, x mod 2^(8*k+8) = x mod 2^(8*k) + 2^(8*k) * byte x k.
Proof.
  intros. unfold byte. rewrite N.shiftr_div_pow2.
  rewrite N.pow_add_r.
  rewrite (N.Div0.mod_mul_r x (2^(8*k)) (2^8)).
  lia.
Qed.

Lemma low_bytes_ge: ∀ n x, (∀ k, k < N.of_nat n -> byte x k ≠ 0) -> Ln n <= x mod 2^(8*N.of_nat n).
Proof.
  induction n; intros x H. apply N.le_0_l.
  rewrite Nat2N.inj_succ in H. rewrite Nat2N.inj_succ, N.mul_succ_r, mod_split8. change (Ln (S n)) with (Ln n + 2^(8*N.of_nat n)).
  assert (A: ∀ k, k < N.of_nat n -> byte x k ≠ 0) by (intros k K; apply H; lia).
  specialize (IHn x A). assert (B: byte x (N.of_nat n) ≠ 0) by (apply H; lia). nia.
Qed.

Lemma testbit_ge_bound: ∀ y W i, y < 2^W -> W <= i -> N.testbit y i = false.
Proof.
  intros y W i Y I. destruct (N.eq_dec y 0) as [->|NZ]. apply N.bits_0.
  apply N.bits_above_log2. apply N.log2_lt_pow2 in Y; lia.
Qed.

Definition K8 : N := 0xfefefefefefefeff.
Definition H8 : N := 0x8080808080808080.

Lemma K8_mod: ∀ j, j < 8 -> K8 mod 2^(8*j+8) = 255*2^(8*j) - Ln (N.to_nat j).
Proof.
  intros j J. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) as JS by lia.
  destruct JS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; vm_compute; reflexivity.
Qed.

Lemma H8_bit: ∀ j, j < 8 -> N.testbit H8 (8*j+7) = true.
Proof.
  intros j J. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) as JS by lia.
  destruct JS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; vm_compute; reflexivity.
Qed.

Lemma Ln_le: ∀ n, Ln n <= 2^(8*N.of_nat n).
Proof.
  induction n. apply N.le_0_l.
  change (Ln (S n)) with (Ln n + 2^(8*N.of_nat n)).
  rewrite Nat2N.inj_succ, N.mul_succ_r, N.pow_add_r. change (2^8) with 256. lia.
Qed.

Lemma top_byte: ∀ k lo L, L <= lo -> lo < 2^k -> L <= 2^k ->
  N.testbit ((lo + (255*2^k - L)) mod 2^(k+8)) (k+7) = true.
Proof.
  intros k lo L A B C.
  assert (P: 0 < 2^k) by (apply N.neq_0_lt_0, N.pow_nonzero; discriminate).
  rewrite N.pow_add_r. change (2^8) with 256.
  rewrite N.mod_small by nia.
  replace (k+7) with (7+k) by lia. rewrite <- N.shiftr_spec', N.shiftr_div_pow2.
  replace ((lo + (255 * 2 ^ k - L)) / 2 ^ k) with 255. reflexivity.
  apply N.div_unique with (r := lo - L); nia.
Qed.

Lemma core: ∀ j x, j < 8 -> (∀ k, k < j -> byte x k ≠ 0) -> byte x j = 0 ->
  N.testbit (N.land (N.land ((x + K8) mod 2^64) (N.lnot x 64)) H8) (8*j+7) = true.
Proof.
  intros j x J LOW Z.
  assert (LO := low_bytes_ge (N.to_nat j) x). rewrite N2Nat.id in LO. specialize (LO LOW).
  assert (LB := N.mod_lt x (2^(8*j)) ltac:(apply N.pow_nonzero; discriminate)).
  assert (LL := Ln_le (N.to_nat j)). rewrite N2Nat.id in LL.
  assert (S8 := mod_split8 x j). rewrite Z, N.mul_0_r, N.add_0_r in S8.
  set (lo := x mod 2^(8*j)) in *.
  rewrite !N.land_spec, N.lnot_spec_low, H8_bit by lia.
  replace (N.testbit x (8*j+7)) with false.
  2:{ rewrite <- (N.mod_pow2_bits_low x (8*j+8)) by lia. rewrite S8. symmetry. apply (testbit_ge_bound _ (8*j)); lia. }
  rewrite N.mod_pow2_bits_low by lia.
  rewrite <- (N.mod_pow2_bits_low (x+K8) (8*j+8)) by lia.
  rewrite <- N.Div0.add_mod_idemp_l, S8, <- N.Div0.add_mod_idemp_r, K8_mod by exact J.
  rewrite top_byte by assumption. reflexivity.
Qed.

(* the word-at-a-time zero test: if it reports no zero byte, there is none *)
Theorem haszero_none: ∀ x,
  N.land (N.land ((x + K8) mod 2^64) (N.lnot x 64)) H8 = 0 ->
  ∀ i, i < 8 -> byte x i ≠ 0.
Proof.
  intros x T.
  assert (ST: ∀ j, j < 8 -> (∀ k, k < j -> byte x k ≠ 0) -> byte x j ≠ 0).
  { intros j J LOW Z. pose proof (core j x J LOW Z) as C. rewrite T, N.bits_0 in C. discriminate. }
  assert (A: ∀ n, (n <= 8)%nat -> ∀ k, k < N.of_nat n -> byte x k ≠ 0).
  { induction n; intros N8 k K. lia.
    rewrite Nat2N.inj_succ in K. destruct (N.lt_ge_cases k (N.of_nat n)) as [L|G].
    - apply IHn; [lia | exact L].
    - replace k with (N.of_nat n) by lia. apply ST. lia. apply IHn. lia. }
  intros i I. apply (A 8%nat). lia. exact I.
Qed.
