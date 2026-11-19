From Stdlib Require Import NArith Lia.

Open Scope N.

Definition divstep (b k q r : N) : N * N :=
  if b * 2^k <=? r then (2*q + 1, r - b*2^k) else (2*q, r).

Lemma divstep_sound (b k q r n : N) :
  0 < b -> n < 2^32 ->
  r < b * 2^(k+1) ->
  n = b * (q * 2^(k+1)) + r ->
  let '(q', r') := divstep b k q r in
  n = b * (q' * 2^k) + r' /\ r' < b * 2^k /\ q' * 2^k < 2^32.
Proof.
  intros B NB HR HN.
  assert (HP : 2^(k+1) = 2 * 2^k).
  { rewrite N.pow_add_r, N.pow_1_r. nia. }
  rewrite HP in HR, HN. unfold divstep.
  destruct (b * 2^k <=? r) eqn:E.
  - apply N.leb_le in E. cbv beta iota. split.
    + replace (b * (q * (2 * 2^k))) with (2*q*(b*2^k)) in HN by ring.
      replace (b * ((2*q + 1) * 2^k)) with (2*q*(b*2^k) + b*2^k) by ring.
      rewrite HN.
      replace (2*q*(b*2^k) + b*2^k + (r-b*2^k))
        with (2*q*(b*2^k) + ((r-b*2^k)+b*2^k)) by ring.
      rewrite N.sub_add by exact E. reflexivity.
    + split; [lia|].
      assert (HD : 2^k <= b*2^k).
      { rewrite <- (N.mul_1_l (2^k)) at 1. apply N.mul_le_mono_r. lia. }
      eapply N.le_lt_trans with (m := 2*q*(b*2^k) + 2^k); [|lia].
      replace ((2*q+1)*2^k) with ((2*q)*2^k + 2^k) by ring.
      apply N.add_le_mono_r. apply N.mul_le_mono_l.
      rewrite <- (N.mul_1_l (2^k)) at 1. apply N.mul_le_mono_r. lia.
  - apply N.leb_gt in E. cbv beta iota. split.
    + replace (b * (q * (2 * 2^k))) with (q*(2*(b*2^k))) in HN by ring.
      replace (b * ((2*q) * 2^k)) with (q*(2*(b*2^k))) by ring.
      exact HN.
    + split; [exact E|].
      eapply N.le_lt_trans with (m := b * (q * (2*2^k))); [|nia].
      replace ((2*q)*2^k) with (q*(2*2^k)) by ring.
      rewrite <- (N.mul_1_l (q*(2*2^k))) at 1.
      apply N.mul_le_mono_r. lia.
Qed.

Lemma divstep_previous_bound (b k : N) :
  0 < k -> b * 2^k < 2^32 -> b * 2^(k-1) < 2^32.
Proof.
  intros HK HB.
  eapply N.le_lt_trans with (m := b * 2^k); [|exact HB].
  apply N.mul_le_mono_l. apply N.pow_le_mono_r; lia.
Qed.

Lemma divstep_qmod (q q' : N) :
  2*q = q' -> 2*q < 2^32 -> (q+q) mod 2^32 = q'.
Proof.
  intros Q H. rewrite <- Q, N.mod_small by lia. lia.
Qed.

Lemma divstep_qmod1 (q q' : N) :
  2*q+1 = q' -> 1+q+q = q'.
Proof.
  intros Q. rewrite <- Q. lia.
Qed.

Lemma divstep_rmod (r d r' : N) :
  r < 2^32 -> r-d = r' -> (r-d) mod 2^32 = r'.
Proof.
  intros H R. rewrite <- R, N.mod_small by lia. reflexivity.
Qed.
