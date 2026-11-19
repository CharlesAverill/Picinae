From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import signed_div_stages.
Import ARM7Notations.
Open Scope N.

Definition div_general_k (n b : N) : N := N.log2 n - N.log2 b.

Lemma div_general_index (n b : N) :
  0 < b -> b < n -> n < 2^32 ->
  31 - ((32-N.size b) - (32-N.size n)) = 31-div_general_k n b.
Proof.
  intros B BN NB. unfold div_general_k.
  rewrite !N.size_log2 by lia.
  pose proof (N.log2_le_mono b n ltac:(lia)).
  pose proof (proj1 (N.log2_lt_pow2 n 32 ltac:(lia)) NB).
  pose proof (N.log2_spec b B) as [BL0 BU0]. lia.
Qed.

Lemma div_general_entry (n b : N) :
  n < 2^32 -> 0 < b -> b < n ->
  div_general_k n b <= 31 /\ div_inv n b (div_general_k n b) 0 n.
Proof.
  intros NB B BN.
  pose proof (N.log2_spec n ltac:(lia)) as [NL NU].
  pose proof (N.log2_spec b B) as [BL BU].
  rewrite <- !N.add_1_r in NU, BU.
  pose proof (N.log2_le_mono b n ltac:(lia)) as LM.
  pose proof (proj1 (N.log2_lt_pow2 n 32 ltac:(lia)) NB) as N32.
  unfold div_general_k.
  assert (K31 : N.log2 n - N.log2 b <= 31) by lia.
  split; [exact K31|]. unfold div_inv.
  repeat split; try assumption; try lia.
  - eapply N.lt_le_trans with (m := 2^(N.log2 n+1)); [exact NU|].
    replace (N.log2 n+1) with (N.log2 b+(N.log2 n-N.log2 b+1)) by lia.
    rewrite N.pow_add_r. apply N.mul_le_mono_r. exact BL.
  - eapply N.lt_le_trans with
      (m := 2^(N.log2 b+1) * 2^(N.log2 n-N.log2 b)).
    + apply (N.mul_lt_mono_pos_r
        (2^(N.log2 n-N.log2 b)) b (2^(N.log2 b+1))).
      * pose proof (N.pow_nonzero 2 (N.log2 n-N.log2 b)); lia.
      * exact BU.
    + rewrite <- N.pow_add_r.
      replace (N.log2 b+1+(N.log2 n-N.log2 b)) with (N.log2 n+1) by lia.
      apply N.pow_le_mono_r; lia.
Qed.

Lemma div_pow2_index (b : N) :
  0 < b -> b < 2^32 -> msub 8 (N.size b) 1 = N.log2 b.
Proof.
  intros B BB. rewrite N.size_log2 by lia.
  rewrite msub_sub by lia.
  rewrite N.sub_1_r, N.pred_succ.
  apply N.mod_small.
  pose proof (proj1 (N.log2_lt_pow2 b 32 B) BB). lia.
Qed.


Lemma div_general_addr (n b : N) :
  0 < b -> b < n -> n < 2^32 ->
  0x304b0 ⊕ (msub 28 (31+N.size b) (N.size n) * 2^4) =
  divstage_addr (div_general_k n b).
Proof.
  intros B BN NB. assert (BN0 : 0 < n) by lia.
  pose proof (N.log2_le_mono b n ltac:(lia)) as LM.
  pose proof (proj1 (N.log2_lt_pow2 n 32 BN0) NB) as NU.
  pose proof (div_general_entry n b NB B BN) as [K31 _].
  unfold divstage_addr. rewrite !N.size_log2 by lia.
  rewrite msub_sub by (unfold div_general_k; lia).
  replace (31+N.succ (N.log2 b)-N.succ (N.log2 n))
    with (31-div_general_k n b) by (unfold div_general_k; lia).
  rewrite N.mod_small by (unfold div_general_k; lia).
  replace 16 with (2^4) by reflexivity.
  rewrite N.mod_small by (unfold div_general_k in *; nia).
  rewrite (N.mul_comm (2^4) (31-div_general_k n b)). reflexivity.
Qed.
