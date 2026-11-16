(* GrokBits: word-at-a-time ("has a zero byte") lemmas used by musl's
   C string functions on aarch64.

   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith ZArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* byte i of x (little-endian) *)
Definition byte_of (x i : N) := (x >> (8*i)) mod 2^8.

(* ones8 j = 0x0101...01 with j bytes *)
Definition ones8 (j:N) := N.iter j (fun y => y * 256 + 1) 0.

Lemma ones8_succ: ∀ j, ones8 (N.succ j) = ones8 j * 256 + 1.
Proof. intros. unfold ones8. rewrite N.iter_succ. reflexivity. Qed.

Lemma byte_of_div: ∀ x i, byte_of (x / 2^8) i = byte_of x (N.succ i).
Proof.
  intros. unfold byte_of. rewrite <- N.shiftr_div_pow2, N.shiftr_shiftr.
  f_equal. f_equal. lia.
Qed.

(* If the low j bytes of x are all non-zero, then x mod 2^(8j) >= 0x0101..01. *)
Lemma low_bytes_ge:
  ∀ j x, (∀ i, i < j -> byte_of x i ≠ 0) -> ones8 j <= x mod 2^(8*j).
Proof.
  induction j using N.peano_ind; intros x H.
  - apply N.le_0_l.
  - rewrite ones8_succ.
    replace (8 * N.succ j) with (8 + 8*j) by lia. rewrite N.pow_add_r, N.Div0.mod_mul_r.
    assert (B0: x mod 2^8 ≠ 0).
      specialize (H 0 ltac:(lia)). unfold byte_of in H. rewrite N.mul_0_r, N.shiftr_0_r in H. exact H.
    assert (IH: ones8 j <= (x / 2^8) mod 2^(8*j)).
      apply IHj. intros i Hi. rewrite byte_of_div. apply H. lia.
    change (2^8) with 256 in *. lia.
Qed.

Lemma byte_of_lt: ∀ x i, byte_of x i < 2^8.
Proof. intros. apply mp2_mod_lt. Qed.

(* x mod 2^(8j+8) = x mod 2^(8j) when byte j of x is zero. *)
Lemma mod_byte_zero:
  ∀ x j, byte_of x j = 0 -> x mod 2^(8*j+8) = x mod 2^(8*j).
Proof.
  intros x j H. rewrite N.pow_add_r, N.Div0.mod_mul_r.
  unfold byte_of in H. rewrite N.shiftr_div_pow2 in H. rewrite H. lia.
Qed.

Lemma testbit_one_at: ∀ S b, 2^b <= S -> S < 2^(N.succ b) -> N.testbit S b = true.
Proof.
  intros S b H1 H2.
  assert (Q: 1 = S / 2^b).
    apply N.div_unique with (r := S - 2^b).
    rewrite N.pow_succ_r' in H2. lia.
    lia.
  pose proof (N.testbit_spec' S b) as T. rewrite <- Q in T.
  destruct (N.testbit S b); [reflexivity|discriminate].
Qed.

(* Core fact, for one concrete position j: if the bytes below j are non-zero
   and byte j is zero, then bit 8j+7 of x - 0x0101..01 (mod 2^64) is set. *)
Lemma sub_ones_bit:
  ∀ x j, x < 2^64 -> j < 8 ->
    (∀ i, i < j -> byte_of x i ≠ 0) -> byte_of x j = 0 ->
    N.testbit (msub 64 x 0x0101010101010101) (8*j+7) = true.
Proof.
  intros x j X64 J8 LOW ZJ.
  assert (L := low_bytes_ge j x LOW).
  assert (LT := mp2_mod_lt x (8*j)).
  unfold msub. change (0x0101010101010101 mod 2^64) with 0x0101010101010101.
  rewrite <- (N.mod_pow2_bits_low _ (8*j+8)) by lia.
  rewrite mp2_mod_mod_min, N.min_r by lia.
  rewrite N.Div0.add_mod, (mod_byte_zero x j ZJ).
  assert (J: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  set (L0 := x mod 2^(8*j)) in *. clearbody L0.
  destruct J as [->|[->|[->|[->|[->|[->|[->| -> ]]]]]]];
    vm_compute (ones8 _) in L; vm_compute ((_ - _) mod _);
    rewrite N.mod_small by (cbn in *; lia);
    apply testbit_one_at; cbn in *; lia.
Qed.

(* Contrapositive form used by strlen: if the "has zero byte" test of the
   word x comes out zero, then every byte of x is non-zero. *)
Theorem haszero_test_zero:
  ∀ x, x < 2^64 ->
    ((msub 64 x 0x0101010101010101) .& (x .^ (2^64 - 1)) .& 0x8080808080808080 =? 0) = true ->
    ∀ i, i < 8 -> byte_of x i ≠ 0.
Proof.
  intros x X64 T i. apply N.eqb_eq in T.
  induction i as [i IH] using (well_founded_induction N.lt_wf_0). intros I8 Z.
  assert (B: N.testbit ((msub 64 x 0x0101010101010101) .& (x .^ (2^64 - 1)) .& 0x8080808080808080) (8*i+7) = true).
  { rewrite !N.land_spec, N.lxor_spec.
    rewrite sub_ones_bit; try assumption.
    2: intros k Hk; apply IH; lia.
    assert (XB: N.testbit x (8*i+7) = false).
    { replace (N.testbit x (8*i+7)) with (N.testbit (byte_of x i) 7).
      rewrite Z. reflexivity.
      unfold byte_of. rewrite N.mod_pow2_bits_low by lia. rewrite N.shiftr_spec'. f_equal. lia. }
    rewrite XB.
    replace (2^64 - 1) with (N.ones 64) by reflexivity. rewrite N.ones_spec_low by lia.
    assert (J: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct J as [->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]; reflexivity. }
  rewrite T in B. discriminate B.
Qed.

(* Bytes of a little-endian quadword in memory. *)
Lemma byte_of_qword: ∀ m a i, i < 8 -> byte_of (m Ⓠ[a]) i = m Ⓑ[a + i].
Proof.
  intros m a i I8. unfold byte_of.
  assert (J: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  replace (8*i) with (i*8) by lia.
  rewrite getmem_shiftr8. change (2^8) with (2^(1*8)). rewrite getmem_mod.
  rewrite N.add_comm.
  destruct J as [->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]; reflexivity.
Qed.

(* ---- memchr support (word-at-a-time byte search) ---- *)

Lemma byte_of_xor: ∀ x y i, byte_of (x .^ y) i = byte_of x i .^ byte_of y i.
Proof.
  intros. unfold byte_of. apply N.bits_inj. intro b.
  rewrite N.lxor_spec.
  destruct (N.lt_ge_cases b 8).
  - rewrite !N.mod_pow2_bits_low by lia. rewrite !N.shiftr_spec', N.lxor_spec. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma splat_case: ∀ c D Q R, c < 256 -> 0 < D ->
  0x0101010101010101 = D*(256*Q+1) + R -> 255*R < D ->
  (c*0x0101010101010101 / D) mod 256 = c.
Proof.
  intros c D Q R C DP E RD.
  rewrite <- (N.div_unique (c*0x0101010101010101) D (c*(256*Q+1)) (c*R)); [| nia | rewrite E; nia].
  symmetry; apply N.mod_unique with (q := c*Q); lia.
Qed.

Lemma byte_of_splat: ∀ c i, c < 2^8 -> i < 8 -> byte_of (c * 0x0101010101010101) i = c.
Proof.
  intros c i C I. unfold byte_of. rewrite N.shiftr_div_pow2. change (2^8) with 256 in *.
  assert (J: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct J as [->|[->|[->|[->|[->|[->|[->| -> ]]]]]]];
  match goal with |- (_ / 2^?E) mod _ = _ =>
    let D := eval vm_compute in (2^E) in
    change (2^E) with D;
    apply (splat_case c D (0x0101010101010101 / D / 256) (0x0101010101010101 mod D));
    [ exact C | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ]
  end.
Qed.

Lemma scast_small32: ∀ x, x < 2^31 -> scast 32 64 x = x.
Proof.
  intros x H. unfold scast.
  rewrite (proj1 (toZ_nonneg 32 x)) by (rewrite N.mod_small; cbn in *; lia).
  rewrite N.mod_small by (cbn in *; lia).
  unfold ofZ. rewrite Z.mod_small. apply N2Z.id.
  split. lia. change (2 ^ Z.of_N 64)%Z with (Z.of_N (2^64)). apply N2Z.inj_lt. cbn in *; lia.
Qed.

Lemma xor_nz_neq: ∀ a b, a .^ b ≠ 0 -> a ≠ b.
Proof. intros a b H E. subst. rewrite N.lxor_nilpotent in H. contradiction. Qed.

Lemma addmod_inj: ∀ p k e, k < 2^64 -> e < 2^64 -> p ⊕ k = p ⊕ e -> k = e.
Proof.
  intros p k e K E H. rewrite (N.Div0.add_mod p k), (N.Div0.add_mod p e) in H.
  assert (A := N.mod_lt p (2^64) ltac:(discriminate)).
  set (a := p mod 2^64) in *. clearbody a.
  rewrite (N.mod_small k), (N.mod_small e) in H by assumption.
  zify. Z.div_mod_to_equations. nia.
Qed.

(* If the "has zero byte" test of (splat c) xor w comes out zero, no byte of
   the quadword at a equals c. *)
Theorem hasbyte_test_zero:
  ∀ m a c, c < 2^8 ->
    ((msub 64 (c * 0x0101010101010101 .^ m Ⓠ[a]) 0x0101010101010101)
       .& ((c * 0x0101010101010101 .^ m Ⓠ[a]) .^ 18446744073709551615)
       .& 0x8080808080808080 =? 0) = true ->
    ∀ i, i < 8 -> m Ⓑ[a + i] ≠ c.
Proof.
  intros m a c C T i I.
  assert (X: c * 0x0101010101010101 .^ m Ⓠ[a] < 2^64).
  { apply logic_op_bound. intros x y b Z1 Z2. rewrite N.lxor_spec, Z1, Z2. reflexivity.
    change (2^8) with 256 in C. change (2^64) with 18446744073709551616. lia.
    apply qword_lt64. }
  intro E. apply (haszero_test_zero _ X T i I).
  rewrite byte_of_xor, byte_of_qword, byte_of_splat, E by assumption.
  apply N.lxor_nilpotent.
Qed.
