(* memmove: overlap-aware copy predicates (forward / backward byte and word
   loops) and the arithmetic of the binary's disjointness test.
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFrame GrokFill GrokMem GrokCopy GrokPrefix.
From Grok.proofs Require Import memcpy_defs.
Import ARM8Notations.
Open Scope N.

(* forward copy (d < s): first k dest bytes done, source bytes k.. still original *)
Definition fwd (mem M : memory) (s d n k : N) :=
  (∀ i, i < k -> M Ⓑ[d + i] = mem Ⓑ[s + i]) /\
  (∀ i, k <= i -> i < n -> M Ⓑ[s + i] = mem Ⓑ[s + i]) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = mem Ⓑ[a]).

(* backward copy (s < d): dest bytes k..n-1 done, source bytes ..k-1 still original *)
Definition bwd (mem M : memory) (s d n k : N) :=
  (∀ i, k <= i -> i < n -> M Ⓑ[d + i] = mem Ⓑ[s + i]) /\
  (∀ i, i < k -> M Ⓑ[s + i] = mem Ⓑ[s + i]) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = mem Ⓑ[a]).

Lemma fwd_init: ∀ mem s d n, fwd mem mem s d n 0.
Proof. intros. repeat split; intros; first [lia | reflexivity]. Qed.

Lemma bwd_init: ∀ mem s d n, bwd mem mem s d n n.
Proof. intros. repeat split; intros; first [lia | reflexivity]. Qed.

Lemma fwd_step: ∀ mem M s d n k len v, fwd mem M s d n k -> d < s -> k + len <= n -> 0 < len -> len <= 8 ->
  s + n < 2^64 -> d + n < 2^64 -> (∀ j, j < len -> byte v j = mem Ⓑ[s + k + j]) ->
  fwd mem (setmem 64 LittleE len M (d + k) v) s d n (k + len).
Proof.
  intros mem M s d n k len v [H1 [H2 H3]] DS K L0 L8 S D V. repeat split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H1; exact IK.
    + rewrite read_in by (change (2^64) with 18446744073709551616 in *; lia).
      replace (d + i - (d + k)) with (i - k) by lia. rewrite V by lia.
      apply (f_equal (getmem 64 LittleE 1 mem)). lia.
  - intros i I1 I2. rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H2; lia.
  - intros a A O. rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H3; assumption.
Qed.

Lemma bwd_step: ∀ mem M s d n k len v, bwd mem M s d n (k + len) -> s < d -> k + len <= n -> 0 < len -> len <= 8 ->
  s + n < 2^64 -> d + n < 2^64 -> (∀ j, j < len -> byte v j = mem Ⓑ[s + k + j]) ->
  bwd mem (setmem 64 LittleE len M (d + k) v) s d n k.
Proof.
  intros mem M s d n k len v [H1 [H2 H3]] SD K L0 L8 S D V. repeat split.
  - intros i I1 I2. destruct (N.lt_ge_cases i (k + len)) as [IK|IK].
    + rewrite read_in by (change (2^64) with 18446744073709551616 in *; lia).
      replace (d + i - (d + k)) with (i - k) by lia. rewrite V by lia.
      apply (f_equal (getmem 64 LittleE 1 mem)). lia.
    + rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H1; lia.
  - intros i I. rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H2; lia.
  - intros a A O. rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H3; assumption.
Qed.

Lemma fwd_read: ∀ mem M s d n k j len, fwd mem M s d n k -> k <= j -> j + len <= n ->
  getmem 64 LittleE len M (s + j) = getmem 64 LittleE len mem (s + j).
Proof.
  intros mem M s d n k j len [_ [H2 _]] K J. apply getmem_ext. intros i I.
  replace (s + j + i) with (s + (j + i)) by lia. apply H2; lia.
Qed.

Lemma bwd_read: ∀ mem M s d n k j len, bwd mem M s d n k -> j + len <= k ->
  getmem 64 LittleE len M (s + j) = getmem 64 LittleE len mem (s + j).
Proof.
  intros mem M s d n k j len [_ [H2 _]] J. apply getmem_ext. intros i I.
  replace (s + j + i) with (s + (j + i)) by lia. apply H2; lia.
Qed.

Lemma fwd_done: ∀ mem M s d n, fwd mem M s d n n -> copied mem M s d n.
Proof. intros mem M s d n [H1 [_ H3]]. split; assumption. Qed.

Lemma bwd_done: ∀ mem M s d n, bwd mem M s d n 0 -> copied mem M s d n.
Proof. intros mem M s d n [H1 [_ H3]]. split; [intros i I; apply H1; lia | assumption]. Qed.

Lemma copied_same: ∀ mem s n, copied mem mem s s n.
Proof. intros. split; intros; reflexivity. Qed.

(* value-side helper: bytes of a load from the original source *)
Lemma byte_load: ∀ mem a len j, j < len -> byte (getmem 64 LittleE len mem a) j = mem Ⓑ[a + j].
Proof. intros. rewrite byte_getmem by assumption. apply (f_equal (getmem 64 LittleE 1 mem)). lia. Qed.

Lemma land_m8: ∀ d, d < 2^64 -> N.land d 18446744073709551608 = d - d mod 8.
Proof.
  intros d D.
  replace (d - d mod 8) with (N.shiftl (N.shiftr d 3) 3).
  - rewrite <- N.ldiff_ones_r. apply N.bits_inj. intro k.
    rewrite N.land_spec, N.ldiff_spec.
    replace 18446744073709551608 with (N.ldiff (N.ones 64) (N.ones 3)) by reflexivity.
    rewrite N.ldiff_spec.
    destruct (N.lt_ge_cases k 64) as [K|K].
    + rewrite (N.ones_spec_low 64 k K). destruct (N.testbit d k), (N.testbit (N.ones 3) k); reflexivity.
    + rewrite (N.ones_spec_high 64 k) by lia.
      replace (N.testbit d k) with false; [reflexivity|].
      symmetry. apply (N.bits_above_log2 d k). destruct (N.eq_dec d 0) as [->|NZ]; [simpl; lia|].
      apply N.log2_lt_pow2; [lia | apply N.lt_le_trans with (2^64); [exact D | apply N.pow_le_mono_r; lia]].
  - rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. pose proof (N.div_mod d 8 ltac:(discriminate)).
    change (2^3) with 8. lia.
Qed.

Lemma land7: ∀ d, N.land d 7 = d mod 8.
Proof. intro d. change 7 with (N.ones 3). rewrite N.land_ones. reflexivity. Qed.

(* the disjointness test (s - d - n <= -2n, unsigned) fails when the buffers overlap or n = 0 (d <> s) *)
Lemma mva_branch: ∀ d src n, d + n < 2^64 -> src + n < 2^64 -> n < 2^62 -> d <> src ->
  (n = 0 \/ (d < src + n /\ src < d + n)) ->
  msub 64 0 (N.shiftl n 1) < msub 64 (msub 64 src n) d /\
  (msub 64 (msub 64 src n) d + N.shiftl n 1) mod 2^64 <> 0.
Proof.
  intros d src n D S N NE O.
  rewrite N.shiftl_mul_pow2. change (2^1) with 2.
  assert (M4: 2^64 = 4 * 2^62) by reflexivity.
  assert (MNZ: 2^64 <> 0) by discriminate.
  unfold msub. rewrite (N.mod_small n) by lia. rewrite (N.mod_small d) by lia. rewrite (N.mod_small (n*2)) by lia.
  rewrite !N.add_mod_idemp_l by assumption.
  destruct O as [Z | [O1 O2]].
  - subst n. rewrite N.mul_0_l, N.add_0_r, N.sub_0_r, N.add_0_l, N.mod_same by assumption.
    replace (src + 2^64 + (2^64 - d)) with ((src + (2^64 - d)) + 1 * 2^64) by lia.
    rewrite N.mod_add by assumption.
    destruct (N.lt_ge_cases src d).
    + rewrite N.mod_small by lia. lia.
    + rewrite mod_q1 by lia. lia.
  - assert (NP: 0 < n) by lia.
    rewrite (N.mod_small (0 + (2^64 - n * 2))) by lia.
    rewrite (mod_q1 (src + (2^64 - n) + (2^64 - d))) by lia.
    rewrite (mod_q2 (src + (2^64 - n) + (2^64 - d) + n * 2)) by lia.
    lia.
Qed.

Lemma mod8_up: ∀ a b, a mod 8 = 0 -> b mod 8 = 0 -> a <= b -> a <> b -> a + 8 <= b.
Proof.
  intros a b A B L NE. pose proof (N.div_mod a 8 ltac:(discriminate)). pose proof (N.div_mod b 8 ltac:(discriminate)). lia.
Qed.

Lemma sub_mod8: ∀ a, (a - a mod 8) mod 8 = 0.
Proof.
  intro a. pose proof (N.div_mod a 8 ltac:(discriminate)) as E.
  replace (a - a mod 8) with ((a / 8) * 8) by lia. apply N.mod_mul. discriminate.
Qed.

Lemma mod8_down: ∀ x x0, x0 <= x -> (x - x0) mod 8 = 0 -> x mod 8 <= x0 -> x0 <> x mod 8 ->
  x mod 8 + 8 <= x0 /\ (x - (x0 - 8)) mod 8 = 0.
Proof.
  intros x x0 L M R NE.
  pose proof (N.div_mod x 8 ltac:(discriminate)). pose proof (N.div_mod (x - x0) 8 ltac:(discriminate)).
  pose proof (N.mod_lt x 8 ltac:(discriminate)).
  assert (x mod 8 + 8 <= x0) by lia. split. assumption.
  replace (x - (x0 - 8)) with ((x - x0) + 1 * 8) by lia. rewrite N.mod_add by discriminate. assumption.
Qed.

Lemma mod8_add8: ∀ a, a mod 8 = 0 -> (a + 8) mod 8 = 0.
Proof. intros a A. replace (a + 8) with (a + 1 * 8) by lia. rewrite N.mod_add by discriminate. exact A. Qed.

(* the disjointness test succeeds for disjoint buffers *)
Lemma mvb_disj: ∀ d src n, d + n < 2^64 -> src + n < 2^64 -> n < 2^62 -> 0 < n ->
  (src + n <= d \/ d + n <= src) ->
  msub 64 (msub 64 src n) d <= msub 64 0 (N.shiftl n 1 mod 2^64).
Proof.
  intros d src n D S N P O.
  rewrite N.shiftl_mul_pow2. change (2^1) with 2.
  unfold msub. change (2^64) with 18446744073709551616 in *. change (2^62) with 4611686018427387904 in *.
  rewrite (N.mod_small (n*2)) by lia. rewrite (N.mod_small (n*2)) by lia.
  rewrite (N.mod_small n) by lia. rewrite (N.mod_small d) by lia.
  rewrite !N.add_mod_idemp_l by discriminate.
  pose proof (N.div_mod (src + (18446744073709551616 - n) + (18446744073709551616 - d)) 18446744073709551616 ltac:(discriminate)).
  pose proof (N.mod_lt (src + (18446744073709551616 - n) + (18446744073709551616 - d)) 18446744073709551616 ltac:(discriminate)).
  pose proof (N.div_mod (0 + (18446744073709551616 - n * 2)) 18446744073709551616 ltac:(discriminate)).
  pose proof (N.mod_lt (0 + (18446744073709551616 - n * 2)) 18446744073709551616 ltac:(discriminate)).
  lia.
Qed.

