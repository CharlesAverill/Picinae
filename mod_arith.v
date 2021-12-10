Require Import Etacs.
Require Import Utf8.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_theory.

Ltac trivial2 := solve [reflexivity|discriminate|eassumption].

Definition absdist a b :=
  if a <=? b then b - a else a - b.

Definition modabsdist n a b :=
  absdist (a mod n) (b mod n).

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

Lemma lt_sub: forall a b c,
  a < c -> a - b < c.
Proof.
  intros. eapply N.le_lt_trans; [|eassumption]. apply N.le_sub_l.
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

Lemma mod_sub_extract: forall a b m, m ≠ 0 -> b ≠ 0 -> b <= m ->
  (m + a - b) mod m = (a mod m + (m - b)) mod m.
Proof.
  intros.
  assert (m - b < m). apply conv_lt_sub_lt_add_r.
    destruct (N.eq_0_gt_0_cases m); [contradiction H|assumption].
    apply N.lt_add_pos_r. destruct (N.eq_0_gt_0_cases b);
    [contradiction H0|assumption].
  rewrite N.add_sub_swap, N.add_mod, N.add_comm, (N.mod_small (m - b)) by assumption.
  reflexivity.
Qed.

Theorem absdist_symm: forall a b, absdist a b = absdist b a.
Proof.
  intros. unfold absdist.
  destruct (a <=? b) eqn: LE1, (b <=? a) eqn: LE2; try reflexivity.
  - rewrite N.leb_le in *. einstantiate trivial N.le_antisymm. subst.
    reflexivity.
  - rewrite N.leb_gt in *. assert (b < b). eapply N.lt_trans; eassumption.
    destruct (N.lt_irrefl _ H).
Qed.

Theorem modabsdist_symm: forall n a b, modabsdist n a b = modabsdist n b a.
Proof. intros. unfold modabsdist. apply absdist_symm. Qed.

Theorem modabsdist_eq_absdist: forall n a b,
  a < n -> b < n -> modabsdist n a b = absdist a b.
Proof.
  intros. unfold modabsdist, absdist.
  repeat rewrite N.mod_small by assumption. reflexivity.
Qed.

Theorem modl_modabsdist: forall n a b, (n <> 0) ->
  modabsdist n (a mod n) b = modabsdist n a b.
Proof.
  intros. unfold modabsdist. rewrite N.mod_mod by assumption. reflexivity.
Qed.

Theorem modr_modabsdist: forall n a b, (n <> 0) ->
  modabsdist n a (b mod n) = modabsdist n a b.
Proof.
  intros. unfold modabsdist. rewrite N.mod_mod by assumption. reflexivity.
Qed.

Theorem sub_comm: forall a b c, a - b - c = a - c - b.
Proof.
  intros. rewrite <- N.sub_add_distr, <- N.sub_add_distr, N.add_comm.
  reflexivity.
Qed.

Lemma div_0_l: forall a, 0 / a = 0.
Proof. intros. destruct a; reflexivity. Qed.

Theorem div_eucl_add_one: forall a n q r (NE: n <> 0)
  (DIV: N.div_eucl a n = (q, r)), N.div_eucl (a + n) n  = (N.succ q, r).
Proof.
  intros. destruct (N.div_eucl (a + n) n) as [q0 r0] eqn: DIV2.
  specialize (N.div_eucl_spec a n) as SPEC.
  specialize (N.div_eucl_spec (a + n) n) as SPEC2.
  rewrite DIV in SPEC. rewrite DIV2 in SPEC2.
  assert (a mod n = r). unfold N.modulo. rewrite DIV. reflexivity.
  assert ((a + n) mod n = r0). unfold N.modulo. rewrite DIV2. reflexivity.
  assert (r0 = r). subst. erewrite N.add_mod, N.mod_same, N.add_0_r,
    N.mod_mod, N.add_comm, N.mul_comm, N.mod_add, <- H, N.mod_mod by trivial2.
  reflexivity. clear H H0. subst. f_equal.
  rewrite N.add_comm, N.add_assoc, <- (N.mul_1_r n), <- N.mul_add_distr_l,
    N.add_1_l, N.add_cancel_r, N.mul_cancel_l in SPEC2 at 1 by assumption.
  subst. reflexivity.
Qed.

Theorem div_add_one: forall a n (NE: n <> 0),
  (a + n) / n = N.succ (a / n).
Proof.
  intros. destruct (N.div_eucl a n) as [q r] eqn:DIV.
  einstantiate trivial (div_eucl_add_one) as DIV2. unfold N.div.
  rewrite DIV, DIV2. reflexivity.
Qed.

Theorem div_add_distr_le: forall a b n, n <> 0 -> a / n + b / n <= (a + b) / n.
Proof.
  assert (forall k a b n, n <> 0 -> a < n -> (a + N.of_nat k * n) / n + b / n <=
    ((a + N.of_nat k * n) + b) / n). {
    induction k; intros.
    - simpl. rewrite N.add_0_r, N.div_small, N.add_0_l, N.add_comm by trivial2.
      apply N.div_le_mono. trivial2. apply N.le_add_r.
    - rewrite Nat2N.inj_succ, <- N.add_1_l, N.mul_add_distr_r, N.mul_1_l,
      N.add_assoc, (N.add_comm (a + n)), N.add_assoc, div_add_one,
      <- (N.add_assoc _ _ b), (N.add_comm n b), N.add_assoc, div_add_one,
      N.add_succ_l, <- N.succ_le_mono, (N.add_comm _ a) by assumption.
      apply IHk; assumption.
  }

  intros. rewrite (N.div_mod' a n), N.mul_comm, (N.add_comm _ (a mod n)),
    <- (N2Nat.id (a / n)). apply H. assumption. apply N.mod_lt. assumption.
Qed.

Theorem div_add_distr_eq_noovf: forall a b n, a mod n + b mod n < n ->
  a / n + b / n = (a + b) / n.
Proof.
  assert (mod_div: forall a n, ((a mod n) / n) = 0). intros.
    destruct (n == 0). subst. destruct a; reflexivity.
    apply N.div_small. apply N.mod_lt. assumption.

  intros a b n NOFW. destruct (n == 0) as [|NE]. subst. destruct a, b; reflexivity.

  rewrite (N.div_mod' a n), (N.div_mod' b n).
  remember (a / n) as k. remember (b / n) as l. clear Heqk Heql.

  rewrite (N.add_comm (n * k)), (N.add_comm (n * l)),
    (N.mul_comm n), (N.mul_comm n), N.div_add, N.div_add, mod_div, mod_div,
    N.add_0_l, N.add_0_l, N.add_assoc, N.div_add, <- N.add_assoc,
    (N.add_comm (k * n)), N.add_assoc, N.div_add, N.div_small by trivial2.
  reflexivity.
Qed.

Theorem div_squeeze: forall a k n, k * n <= a -> a < n + k * n ->
  a / n = k.
Proof.
  intros. destruct (n == 0). subst. rewrite N.add_0_l, N.mul_0_r in H0.
  destruct (N.nlt_0_r _ H0). rewrite N.mul_comm in *.
  rewrite <- (N.mul_1_r n), <- N.mul_add_distr_l, N.add_1_l in H0 at 1.
  einstantiate trivial N.div_le_lower_bound.
  einstantiate trivial N.div_lt_upper_bound. rewrite N.lt_succ_r in H2.
  apply N.le_antisymm; assumption.
Qed.

Theorem div_add_distr_eq_ovf: forall a b n, (n <> 0) -> n <= a mod n + b mod n ->
  1 + a / n + b / n = (a + b) / n.
Proof.
  assert (mod_div: forall a n, ((a mod n) / n) = 0). intros.
    destruct (n == 0). subst. destruct a; reflexivity.
    apply N.div_small. apply N.mod_lt. assumption.

  intros a b n NE NOFW.

  rewrite (N.div_mod' a n), (N.div_mod' b n).
  remember (a / n) as k. remember (b / n) as l. clear Heqk Heql.

  einstantiate div_squeeze as DIV. rewrite N.mul_1_l. exact NOFW.
  rewrite N.mul_1_l. apply N.add_lt_mono; apply N.mod_lt; assumption.

  rewrite (N.add_comm (n * k)), (N.add_comm (n * l)),
    (N.mul_comm n), (N.mul_comm n), N.div_add, N.div_add, mod_div, mod_div,
    N.add_0_l, N.add_0_l, N.add_assoc, N.div_add, <- (N.add_assoc (_ mod _)),
    (N.add_comm (k * n)), N.add_assoc, N.div_add, DIV by trivial2.
  reflexivity.
Qed.

Theorem le_irrefl: forall x y, 0 < y -> 0 < x -> x <= x - y -> False.
Proof.
  intros. assert (x - y <= x - 1). apply N.sub_le_mono_l.
  apply N.lt_pred_le. assumption. eapply N.lt_irrefl.
  rewrite <- N.le_succ_l, <- N.add_1_r. apply conv_le_add_le_sub_r.
  eapply N.le_trans. exact H1. exact H2. apply N.lt_pred_le. assumption.
Qed.

Theorem sub_sub_distr2: forall a b c, b < c -> a + b - c = a - (c - b).
Proof.
  intros.
  assert (SUM: c = b + (c - b)).
    rewrite N.add_sub_assoc, N.add_sub_swap, N.sub_diag. reflexivity.
    reflexivity. apply N.lt_le_incl. assumption.
  rewrite SUM at 1. rewrite N.sub_add_distr, N.add_sub. reflexivity.
Qed.

Theorem add_mod_noovf_bounded: forall n a b (NZ: n <> 0)
  (NOFW: a mod n <= (a + b) mod n), a mod n + b mod n < n.
Proof.
  intros.
  assert (a mod n < n). apply N.mod_lt. assumption.
  assert (b mod n < n). apply N.mod_lt. assumption.

  (* If a mod n == 0 or b mod n == 0, trivially is less than n *)
  remember (a mod n) as a'. remember (b mod n) as b'.
  destruct (a' == 0). rewrite e, N.add_0_l; assumption.
  destruct (b' == 0). rewrite e, N.add_0_r; assumption. subst.

  (* Assume n <= a mod n + b mod n... *)
  rewrite N.neq_0_lt_0 in n0, n1. rewrite N.add_mod in NOFW by trivial2.
  destruct (N.le_gt_cases n (a mod n + b mod n)) as [CMP|CMP]; try assumption.

  (* Show that this leads to a contradiction *)
  einstantiate div_squeeze. rewrite N.mul_1_l. exact CMP. rewrite N.mul_1_l.
  apply N.add_lt_mono; apply N.mod_lt; assumption.
  rewrite (N.mod_eq (_ + _)), H1, N.mul_1_r, sub_sub_distr2 in NOFW by assumption.
  einstantiate le_irrefl; try exact NOFW; try trivial2.
  apply N.lt_add_lt_sub_r. assumption. destruct H2.
Qed.

Theorem add_mod_ovf_bounded: forall n a b (NZ: n <> 0)
  (NOFW: (a + b) mod n < a mod n), n <= a mod n + b mod n.
Proof.
  intros.
  assert (a mod n < n). apply N.mod_lt. assumption.
  assert (b mod n < n). apply N.mod_lt. assumption.

  (* Assume a mod n + b mod n < n... *)
  rewrite N.add_mod in NOFW by trivial2.
  destruct (N.le_gt_cases n (a mod n + b mod n)) as [CMP|CMP]. assumption.

  (* Show that this leads to a contradiction *)
  rewrite N.mod_small, <- N.add_0_r, <- N.add_lt_mono_l in NOFW by assumption.
  destruct (N.nlt_0_r _ NOFW).
Qed.

Theorem modabsdist_add_l: forall n a b x, n <> 0 ->
  modabsdist n a (b + a) = x -> x = b mod n \/ x = n - b mod n.
Proof.
  unfold modabsdist, absdist. intros.
  assert (a mod n < n). apply N.mod_lt. assumption.
  assert (b mod n < n). apply N.mod_lt. assumption.
  assert (n * (a / n) <= a). rewrite (N.div_mod' a n) at -1. apply N.le_add_r.
  assert (n * (b / n) <= b). rewrite (N.div_mod' b n) at -1. apply N.le_add_r.
  subst. destruct (_ <=? _) eqn: LE.
  - apply N.leb_le in LE. left. assert (DISTR: b / n + a / n = (b + a) / n).
    apply div_add_distr_eq_noovf. rewrite N.add_comm. apply add_mod_noovf_bounded.
    assumption. rewrite N.add_comm. assumption.
    rewrite N.mod_eq, <- DISTR, (N.add_comm (b / n)),
      N.mul_add_distr_l, N.sub_add_distr, <- N.add_sub_assoc, <- N.mod_eq,
      sub_comm, N.add_sub, <- N.mod_eq by assumption.
    reflexivity.
  - apply N.leb_gt in LE. right. einstantiate add_mod_ovf_bounded as OVF.
    eassumption. rewrite N.add_comm. eassumption.
    einstantiate div_add_distr_eq_ovf as DISTR. eassumption.
    rewrite N.add_comm. exact OVF. apply N.lt_eq_cases in OVF.
    destruct OVF as [OVF|EQ].
    + rewrite (N.mod_eq (b + a)), <- DISTR, (N.add_comm _ (a / n)),
      N.mul_add_distr_l, N.sub_add_distr, <- N.add_sub_assoc, <- N.mod_eq,
      (N.add_comm 1), (N.add_comm b), N.mul_add_distr_l, N.sub_add_distr,
      <- N.add_sub_assoc, <- N.mod_eq, N.mul_1_r, <- sub_sub_distr2,
      N.sub_add_distr, N.add_comm, N.add_sub; trivial2.
    + rewrite EQ at 3. rewrite N.add_sub, N.add_comm, N.add_mod, <- EQ,
      N.mod_same, N.sub_0_r; trivial2.
Qed.

Corollary modabsdist_add_r: forall n a b x, n <> 0 ->
  modabsdist n (b + a) a = x -> x = b mod n \/ x = n - b mod n.
Proof.
  intros. rewrite modabsdist_symm in H0. eapply modabsdist_add_l; trivial2.
Qed.

