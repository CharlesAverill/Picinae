Require Import Utf8.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_theory.

Ltac trivial2 := solve [reflexivity|discriminate|eassumption].

Theorem conv_le_add_le_sub_r: forall m n p,
  m <= p - n -> n <= p -> m + n <= p.
Proof.
  intros. erewrite <- N.sub_add; [apply N.add_le_mono_r|]; assumption.
Qed.

Theorem conv_lt_sub_lt_add_r: ∀ n m p : N,
  0 < m -> n < m + p -> n - p < m.
Proof.
  intros. apply <- N.add_lt_mono_r.
  destruct (p ?= n) eqn: CmpPN.
  - rewrite N.sub_add. assumption. intro. rewrite CmpPN in *. discriminate.
  - rewrite N.sub_add. assumption. intro. rewrite CmpPN in *. discriminate.
  - replace (n - p) with 0. apply N.lt_add_pos_l. assumption. symmetry.
    apply N.sub_0_le. rewrite N.compare_antisym in CmpPN. intro Contra.
    rewrite Contra in CmpPN. discriminate.
Qed.

Lemma nonzero_gt_0: forall n, 0 <> n <-> 0 < n.
Proof.
  intros. split; intro Pre.
  - destruct n. exfalso. apply Pre. reflexivity. reflexivity.
  - destruct n. discriminate. intro. discriminate.
Qed.

Lemma le_le_add_l: forall m n p, m <= n -> m <= p + n.
Proof.
  intros. rewrite N.add_comm. eapply N.le_trans. eassumption. apply N.le_add_r.
Qed.

Lemma le_le_add_r: forall m n p, m <= n -> m <= n + p.
Proof.
  intros. rewrite N.add_comm. apply le_le_add_l; assumption.
Qed.

Lemma le_sub_add_r_sub: forall m n p q,
  p + q <= n -> n <= m -> m - n + p <= m - q.
Proof.
  intros.

  apply N.le_add_le_sub_r. rewrite <- N.add_assoc.
  rewrite <- N.add_sub_swap; [|assumption].
  apply N.le_sub_le_add_r, conv_le_add_le_sub_r;
    [|apply le_le_add_l; assumption].
  rewrite <- N.add_sub_assoc; [|assumption].
  apply N.le_add_r.
Qed.

Lemma le_sub_add_r: forall m n p,
  p <= n -> n <= m -> m - n + p <= m.
Proof.
  intros. assert (p + 0 <= n). rewrite N.add_0_r. assumption.
  erewrite <- N.sub_0_r. apply le_sub_add_r_sub; assumption.
Qed.

Lemma lt_sub_lt_pow:
  forall w n m, n < 2^w -> n - m < 2^w.
Proof.
  intros. apply conv_lt_sub_lt_add_r.
  apply nonzero_gt_0, N.neq_sym, N.pow_nonzero. discriminate.
  apply N.lt_lt_add_r. assumption.
Qed.

Lemma mod_small_sub: forall w n m, n < 2^w ->
  m <= n -> (2^w + n - m) mod 2^w = n - m.
Proof.
  intros. rewrite N.add_comm, N.add_sub_swap, N.add_mod,
    N.mod_same, N.add_0_r, N.mod_mod, N.mod_small; try apply N.pow_nonzero;
    try trivial2. apply lt_sub_lt_pow. assumption.
Qed.

Lemma mod_small_sub2: forall m n w, m < 2^w ->
  (m - n) mod 2^w = m - n.
Proof.
  intros. apply N.mod_small, lt_sub_lt_pow. assumption.
Qed.

Lemma sub_sub_distr: forall m n p, p <= n -> n <= m ->
  m - n + p = m - (n - p).
Proof.
  intros. symmetry.

  assert (n <= m + p). apply le_le_add_r. assumption.

  apply N.add_sub_eq_r. rewrite <- N.add_sub_swap, N.add_sub_assoc, N.sub_add,
  N.add_sub; solve [assumption|reflexivity].
Qed.

Lemma mod_small_sub_add: forall m n p w, m < 2^w -> p <= n -> n <= m ->
  (m - n + p) mod 2^w = m - n + p.
Proof.
  intros. rewrite N.mod_small; [reflexivity|].
  rewrite sub_sub_distr; try assumption.
  apply lt_sub_lt_pow. assumption.
Qed.

Lemma fold_pow: forall a b, N.pos (a ^ b) = (N.pos a) ^ (N.pos b).
Proof. reflexivity. Qed.

