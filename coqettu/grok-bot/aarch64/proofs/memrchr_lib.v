(* memrchr scalar path: arithmetic lemmas and VC closers, shared by
   memrchr_proof.v and the strrchr proof (tail call into memrchr).
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon.
From Grok.proofs Require Import memrchr_defs.
Import ARM8Notations.
Open Scope N.

Lemma msub1 x: 0 < x -> x < 2^64 -> msub 64 x 1 = x - 1.
Proof.
  intros. unfold msub. rewrite (N.mod_small 1) by lia.
  replace (x + (2^64 - 1)) with ((x-1) + 1*2^64) by lia.
  rewrite N.mod_add by lia. apply N.mod_small; lia.
Qed.

Lemma c8_small c: c8 c mod 2^32 = c8 c.
Proof.
  unfold c8. apply N.mod_small.
  assert (c mod 2^8 < 2^8) by (apply N.mod_lt; discriminate). lia.
Qed.

Lemma c8_32 c: c mod 2^8 = c8 (c mod 2^32).
Proof.
  unfold c8. rewrite (N.div_mod c (2^32)) at 1 by discriminate.
  replace (2^32 * (c / 2^32) + c mod 2^32) with (c mod 2^32 + (2^24 * (c / 2^32)) * 2^8) by lia.
  apply N.mod_add. discriminate.
Qed.

Lemma nomatch_empty m p c n: nomatch_above m p c n n.
Proof. intros i H1 H2. lia. Qed.

Lemma nomatch_step m p c k n: 0 < k -> m Ⓑ[p + k - 1] ≠ c ->
  nomatch_above m p c k n -> nomatch_above m p c (k - 1) n.
Proof.
  intros K B NM i H1 H2. destruct (N.eq_dec i (k - 1)) as [EQ|NE].
  - subst i. replace (p + (k - 1)) with (p + k - 1) by lia. exact B.
  - apply NM; lia.
Qed.

Ltac bools_to_props_mr := repeat match goal with
 | H: negb _ = true |- _ => apply Bool.negb_true_iff in H
 | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H
 end.

(* entry: NEON block path excluded by the precondition (hypothesis NEON). *)
Ltac mrc_neon NEON :=
  match goal with BC: (if 14 <=? ?n then _ else _) .| _ = _ |- _ =>
    destruct (14 <=? n) eqn:E1; destruct (n =? 14) eqn:E2; cbn in BC; try discriminate;
    bools_to_props_mr; destruct NEON; lia end.

(* entry -> scalar loop with k = n *)
Ltac mrc_enter n :=
  unfold mrc_loop; exists n; split; [lia|]; split; [rewrite msub1 by lia; lia|];
  split; [apply msub1; lia|]; split; [first [reflexivity | apply c8_32]|];
  split; [assumption|]; split; [assumption|]; split; [apply nomatch_empty|];
  repeat split; assumption.

(* loop: cursor reached p-1, return 0 *)
Ltac mrc_null k NM BC :=
  unfold mrc_post; rewrite !N.mod_small in BC by lia; assert (k = 0) by lia; subst k;
  split; [right; split; [reflexivity | exact NM] | repeat split; assumption].

(* loop: byte p+k-1 matches *)
Ltac mrc_found k NM BC BC0 :=
  unfold mrc_post; assert (XP: k <> 0) by (intro; subst k; apply BC; f_equal; lia);
  rewrite c8_small in BC0;
  split; [ left; exists (k - 1); split; [lia|]; split; [lia|]; split;
           [ match goal with |- context [?q + (k - 1)] => replace (q + (k - 1)) with (q + k - 1) by lia end; symmetry; exact BC0
           | replace (k - 1 + 1) with k by lia; exact NM ]
         | repeat split; assumption ].

(* loop: byte p+k-1 does not match, continue with k-1 *)
Ltac mrc_next k NM BC BC0 :=
  unfold mrc_loop; assert (XP: k <> 0) by (intro; subst k; apply BC; f_equal; lia);
  rewrite c8_small in BC0; exists (k - 1); split; [lia|]; split; [rewrite msub1 by lia; lia|];
  repeat split; try assumption; try reflexivity;
  apply nomatch_step; [lia | apply not_eq_sym; exact BC0 | exact NM].
