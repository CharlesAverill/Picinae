(* Architecture-neutral signed division bounds, reused from amd64_common.v.
   Original helpers: Claude Opus 5.5; extracted by GPT-6 Astra (OpenAI).
   No ISA/program-logic imports. *)
From Stdlib Require Import ZArith Lia.

Lemma quot_range:
  forall (n d m:Z), (0 < m)%Z -> (-m <= n < m)%Z -> (-m <= d < m)%Z -> d <> 0%Z ->
  ~ (n = -m /\ d = -1)%Z -> (-m <= Z.quot n d < m)%Z.
Proof.
  intros n d m M RN RD DNZ NOVF.
  destruct (Z.eq_dec d 1) as [->|D1]. rewrite Z.quot_1_r. lia.
  destruct (Z.eq_dec d (-1)) as [->|D2].
    pose proof (Z.quot_opp_r n 1 ltac:(lia)) as Q. simpl (Z.opp 1) in Q. rewrite Q, Z.quot_1_r. lia.
  assert (A: (Z.abs (Z.quot n d) <= Z.abs n / 2)%Z).
    rewrite <- Z.quot_abs, Z.quot_div_nonneg by lia.
    apply Z.div_le_compat_l; lia.
  assert (B: (Z.abs n / 2 <= m / 2)%Z) by (apply Z.div_le_mono; lia).
  assert (C: (m / 2 < m)%Z) by (apply Z.div_lt; lia).
  lia.
Qed.

Lemma rem_range:
  forall (n d m:Z), (-m <= d < m)%Z -> d <> 0%Z -> (-m <= Z.rem n d < m)%Z.
Proof.
  intros. pose proof (Z.rem_bound_abs n d H0). lia.
Qed.
