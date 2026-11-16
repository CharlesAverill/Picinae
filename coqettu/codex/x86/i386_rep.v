(* Counted operational invariants for intra-instruction loops. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia List.
Import X86Notations.
Open Scope N.

Lemma eval_var_value : forall c s v w n,
  c v = Some w -> s v = n -> eval_exp c s (Var v) n w.
Proof. intros c s v w n TYPE VALUE. subst n. apply EVar. exact TYPE. Qed.

Lemma iter_exec_indexed : forall limit q (P : N -> typctx -> store -> Prop),
  (forall i c s c' s' x, i < limit -> P i c s ->
    exec_stmt c s q c' s' x -> x = None /\ P (i+1) c' s') ->
  forall n i c s c' s' x, i+n <= limit -> P i c s ->
    exec_stmt c s (N.iter n (Seq q) Nop) c' s' x ->
    x = None /\ P (i+n) c' s'.
Proof.
  intros limit q P STEP n. induction n using N.peano_ind;
    intros i c s c' s' x BOUND PRE XS.
  - inversion XS; subst. rewrite N.add_0_r. split; [reflexivity|exact PRE].
  - rewrite Niter_succ in XS. inversion XS; subst.
    + match goal with H : exec_stmt c s q _ _ (Some _) |- _ =>
        destruct (STEP i _ _ _ _ _ ltac:(clear - BOUND; lia) PRE H) as [NO _];
        discriminate NO end.
    + match goal with H : exec_stmt c s q ?c2 ?s2 None,
                      REST : exec_stmt ?c2 ?s2 (N.iter n (Seq q) Nop) _ _ _ |- _ =>
        destruct (STEP i _ _ _ _ _ ltac:(clear - BOUND; lia) PRE H) as [_ POST];
        replace (i+N.succ n) with ((i+1)+n) by lia;
        eapply IHn; [clear - BOUND; lia | exact POST | exact REST]
      end.
Qed.

Lemma exec_seq_prefix : forall c s q1 q2 cm sm c' s' x,
  exec_stmt c s q1 cm sm None ->
  exec_stmt c s (Seq q1 q2) c' s' x ->
  forall_exps_in_stmt not_unknown q1 ->
  exec_stmt cm sm q2 c' s' x.
Proof.
  intros c s q1 q2 cm sm c' s' x FIRST XS NU. inversion XS; subst.
  - match goal with H : exec_stmt c s q1 _ _ (Some _) |- _ =>
      pose proof (exec_stmt_deterministic NU FIRST H) as EQ; discriminate EQ end.
  - match goal with H : exec_stmt c s q1 ?c2 ?s2 None,
                    REST : exec_stmt ?c2 ?s2 q2 c' s' x |- _ =>
      pose proof (exec_stmt_deterministic NU FIRST H) as EQ;
      inversion EQ; subst; exact REST end.
Qed.

Lemma exec_if_guard : forall c s e q1 q2 b c' s' x,
  eval_exp c s e b 1 ->
  exec_stmt c s (If e q1 q2) c' s' x ->
  forall_exps_in_exp not_unknown e ->
  exec_stmt c s (match b with 0 => q2 | _ => q1 end) c' s' x.
Proof.
  intros c s e q1 q2 b c' s' x GUARD XS NU. inversion XS; subst.
  match goal with E : eval_exp c s e _ 1 |- _ =>
    pose proof (eval_exp_deterministic NU GUARD E) as EQ;
    inversion EQ; subst; assumption end.
Qed.

Lemma exec_move_var : forall c s destination source value width c' s' x,
  c source = Some width -> s source = value ->
  exec_stmt c s (Move destination (Var source)) c' s' x ->
  x = None /\ s' = s[destination := value].
Proof.
  intros c s destination source value width c' s' x TYPE VALUE XS.
  assert (RUN : exec_stmt c s (Move destination (Var source))
    (c[destination := Some width]) (s[destination := value]) None).
  { apply XMove. eapply eval_var_value; eassumption. }
  assert (NU : forall_exps_in_stmt not_unknown (Move destination (Var source)))
    by repeat split.
  pose proof (exec_stmt_deterministic NU XS RUN) as EQ.
  inversion EQ; subst. split; reflexivity.
Qed.
