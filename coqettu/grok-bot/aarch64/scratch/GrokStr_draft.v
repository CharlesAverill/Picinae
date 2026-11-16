(* GrokStr: byte-copy model and the word-at-a-time zero-byte test used by musl's
   stpcpy/strcpy on aarch64.  Written by Grok Bot (agent coqettu) and
   machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Arith Lia Bool.
Require Import Picinae_armv8.
Import ARM8Notations.
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


(* bcp m d s k: memory after copying bytes s+i -> d+i, i = 0..k-1, in order,
   each byte read from the memory produced by the previous copies. *)
Fixpoint bcp (m:N) (d s:N) (k:nat) : N :=
  match k with
  | O => m
  | S k' => let m' := bcp m d s k' in setmem 64 LittleE 1 m' (d + N.of_nat k') (getmem 64 LittleE 1 m' (s + N.of_nat k'))
  end.

(* the i-th source byte, as read by the copy, is non-zero for all i < k *)
Definition bnz (m d s:N) (k:N) := ∀ i, i < k -> getmem 64 LittleE 1 (bcp m d s (N.to_nat i)) (s + i) ≠ 0.

Lemma bnz_succ: ∀ m d s k, bnz m d s k -> getmem 64 LittleE 1 (bcp m d s (N.to_nat k)) (s + k) ≠ 0 -> bnz m d s (k+1).
Proof.
  unfold bnz. intros m d s k NZ B i I.
  destruct (N.lt_ge_cases i k). apply NZ; assumption. replace i with k by lia. exact B.
Qed.

Lemma getmem_byte8: ∀ m a i, i < 8 ->
  getmem 64 LittleE 1 m (a + i) = byte (getmem 64 LittleE 8 m a) i.
Proof.
  intros m a i I. unfold byte.
  replace (getmem 64 LittleE 8 m a) with (getmem 64 LittleE (i + (8-i)) m a) by (f_equal; lia).
  rewrite getmem_split. replace (8*i) with (i*8) by lia. rewrite shiftr_cbits_elim by apply getmem_bound.
  rewrite (getmem_mod 64 LittleE 1). replace (N.min (8-i) 1) with 1 by lia. reflexivity.
Qed.

Lemma msub_shift: ∀ s d K i, msub 64 (s + K + i) (d + K) = (msub 64 s d + i) mod 2^64.
Proof.
  intros. unfold msub.
  pose proof (N.div_mod (d+K) (2^64) ltac:(discriminate)) as D1.
  pose proof (N.div_mod d (2^64) ltac:(discriminate)) as D2.
  pose proof (N.mod_lt (d+K) (2^64) ltac:(discriminate)).
  pose proof (N.mod_lt d (2^64) ltac:(discriminate)).
  assert (Q: d / 2^64 <= (d+K) / 2^64) by (apply N.Div0.div_le_mono; lia).
  rewrite N.Div0.add_mod_idemp_l.
  replace (s + K + i + (2 ^ 64 - (d + K) mod 2 ^ 64))
     with (s + (2 ^ 64 - d mod 2 ^ 64) + i + ((d+K)/2^64 - d/2^64) * 2^64) by nia.
  apply N.Div0.mod_add.
Qed.

Lemma msub_shift_r: ∀ s d K i, msub 64 (d + K) (s + K + i) = msub 64 d (s + i).
Proof.
  intros. unfold msub.
  pose proof (N.div_mod (s+K+i) (2^64) ltac:(discriminate)) as D1.
  pose proof (N.div_mod (s+i) (2^64) ltac:(discriminate)) as D2.
  pose proof (N.mod_lt (s+K+i) (2^64) ltac:(discriminate)).
  pose proof (N.mod_lt (s+i) (2^64) ltac:(discriminate)).
  assert (Q: (s+i) / 2^64 <= (s+K+i) / 2^64) by (apply N.Div0.div_le_mono; lia).
  replace (d + K + (2 ^ 64 - (s + K + i) mod 2 ^ 64))
     with (d + (2 ^ 64 - (s + i) mod 2 ^ 64) + ((s+K+i)/2^64 - (s+i)/2^64) * 2^64) by nia.
  apply N.Div0.mod_add.
Qed.

(* reads at s+K+i are unaffected by the first i byte stores at d+K.. when
   s - d is a multiple of 8 (mod 2^64) and i < 8 *)
Lemma frame8: ∀ m s d K i v, msub 64 s d mod 8 = 0 -> i < 8 ->
  getmem 64 LittleE 1 (setmem 64 LittleE i m (d + K) v) (s + K + i) = getmem 64 LittleE 1 m (s + K + i).
Proof.
  intros m s d K i v A I.
  pose proof (msub_lt 64 s d) as LT.
  pose proof (N.div_mod (msub 64 s d) 8 ltac:(discriminate)) as DM. rewrite A, N.add_0_r in DM.
  assert (SM: (msub 64 s d + i) mod 2^64 = msub 64 s d + i).
  { apply N.mod_small. lia. }
  apply getmem_frame.
  - destruct (N.eq_dec i 0) as [Z|Z]; [right; exact Z | left].
    rewrite msub_shift_r, msub_neg.
    replace (msub 64 (s+i) d) with ((msub 64 s d + i) mod 2^64)
      by (rewrite <- (msub_shift s d 0 i); rewrite !N.add_0_r; reflexivity).
    rewrite SM, N.mod_small by lia. lia.
  - left. rewrite msub_shift, SM. lia.
Qed.


Section Word.
  Variables (m d s w : N) (k : nat).
  Hypothesis (AL: msub 64 s d mod 8 = 0).
  Hypothesis (W: getmem 64 LittleE 8 (bcp m d s k) (s + N.of_nat k) = w).

  Lemma bcp_prefix: ∀ i, (i <= 8)%nat ->
    bcp m d s (k+i) = setmem 64 LittleE (N.of_nat i) (bcp m d s k) (d + N.of_nat k) (w mod 2^(8*N.of_nat i)).
  Proof.
    induction i; intro I.
    - rewrite Nat.add_0_r. simpl. rewrite setmem_0. reflexivity.
    - rewrite Nat.add_succ_r. cbn [bcp]. rewrite IHi by lia.
      rewrite Nat2N.inj_add, !N.add_assoc.
      rewrite frame8 by (assumption || lia).
      rewrite getmem_byte8 by lia. rewrite W.
      rewrite setmem_merge.
      rewrite cbits_add by (apply N.mod_lt; apply N.pow_nonzero; discriminate).
      rewrite Nat2N.inj_succ, <- N.add_1_r.
      f_equal.
      replace (N.of_nat i * 8) with (8 * N.of_nat i) by lia.
      rewrite N.Div0.mod_mod.
      replace (8 * (N.of_nat i + 1)) with (8 * N.of_nat i + 8) by lia.
      rewrite mod_split8. lia.
  Qed.

  Lemma bcp_word_read: ∀ i, (i < 8)%nat ->
    getmem 64 LittleE 1 (bcp m d s (k+i)) (s + N.of_nat (k+i)) = byte w (N.of_nat i).
  Proof.
    intros i I. rewrite bcp_prefix by lia. rewrite Nat2N.inj_add, N.add_assoc.
    rewrite frame8 by (assumption || lia). rewrite getmem_byte8 by lia. rewrite W. reflexivity.
  Qed.

  Lemma bcp_word: bcp m d s (k+8) = setmem 64 LittleE 8 (bcp m d s k) (d + N.of_nat k) w.
  Proof.
    rewrite bcp_prefix by lia. change (N.of_nat 8) with 8. change (2^(8*8)) with (2^(8*8)).
    apply setmem_mod_r.
  Qed.
End Word.
