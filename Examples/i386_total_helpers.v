(* Restore first-exit execution context for the i386 string routines.
   Instruction witness construction is provided by the shared ISA tactics. *)
From Stdlib Require Import Utf8 NArith List.
Require Export Picinae_i386.
Open Scope N.

Lemma i386_eventually_context:
  forall p xp entry t,
    eventually p (fun t' => xp t' = true) t ->
    execution_context p xp entry t ->
    eventually p (fun t' => xp t' = true /\ execution_context p xp entry t') t.
Proof.
  intros p xp entry t EV. induction EV; intros CTX.
  - apply EventuallyHere. split; assumption.
  - destruct (xp (xs::t)) eqn:EX.
    + apply EventuallyHere. split; assumption.
    + destruct CTX as [XP [ORIGIN UT]].
      eapply EventuallyStep. exact ENABLED.
      intros xs' CS. apply H; [exact CS|].
      split. apply exec_prog_step; assumption.
      split. rewrite ostartof_step. exact ORIGIN.
      apply unterminated_cons; assumption.
Qed.
