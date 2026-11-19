(* GrokPrefix: stepping a straight-line instruction prefix one statement at a
   time (with GrokTail.step_satisfies_all) while carrying the `models`
   relation, plus small modular-arithmetic helpers.
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

Lemma models_reset_temps': ∀ s2 s1, models archtyps s2 -> models archtyps (reset_temps s1 s2).
Proof. intros s2 s1 MDL v w H. unfold reset_temps, reset_vars. rewrite H. apply MDL, H. Qed.

Lemma step_models: ∀ p s a sz q c1 s1 x1, welltyped_prog archtyps p -> p s a = Some (sz, q) ->
  models archtyps s -> exec_stmt archtyps s q c1 s1 x1 -> models archtyps (reset_temps s s1).
Proof.
  intros p s a sz q c1 s1 x1 WP LU M XS. specialize (WP s a). rewrite LU in WP. destruct WP as [c' T].
  apply models_reset_temps'. eapply pres_frame_exec_stmt; eassumption.
Qed.

Lemma reset_reg: ∀ s s' v, archtyps v <> None -> reset_temps s s' v = s' v.
Proof. intros s s' v H. unfold reset_temps, reset_vars. destruct (archtyps v); [reflexivity | contradiction]. Qed.

Lemma lor_odd: ∀ x y, (x mod 2 = 1 \/ y mod 2 = 1) -> (N.lor x y) mod 2^1 = 1.
Proof.
  intros x y H. change (2^1) with 2. rewrite <- N.bit0_mod. rewrite N.lor_spec.
  destruct H as [H|H]; rewrite <- N.bit0_mod in H;
    destruct (N.testbit x 0), (N.testbit y 0); cbn in *; congruence.
Qed.

Lemma msub_self: ∀ a, msub 64 a a = 0.
Proof.
  intro a. unfold msub. rewrite <- N.add_mod_idemp_l by discriminate.
  pose proof (N.mod_lt a (2^64) ltac:(discriminate)).
  replace (a mod 2^64 + (2^64 - a mod 2^64)) with (2^64) by lia. apply N.mod_same. discriminate.
Qed.

Lemma mod_q1: ∀ V M, M <> 0 -> M <= V -> V < 2*M -> V mod M = V - M.
Proof. intros V M NZ L H. replace V with ((V - M) + 1*M) at 1 by lia. rewrite N.mod_add by assumption. apply N.mod_small. lia. Qed.

Lemma mod_q2: ∀ V M, M <> 0 -> 2*M <= V -> V < 3*M -> V mod M = V - 2*M.
Proof. intros V M NZ L H. replace V with ((V - 2*M) + 2*M) at 1 by lia. rewrite N.mod_add by assumption. apply N.mod_small. lia. Qed.

