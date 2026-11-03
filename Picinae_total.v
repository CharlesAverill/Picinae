(* Picinae: Platform In Coq for INstruction Analysis of Executables
   Total correctness for trace-dependent invariant sets.

   The inductive eventually predicate follows Definition 1 of Mazzucato et al.,
   "Relational Hoare Logic for Realistically Modelled Machine Code", CAV 2025,
   https://doi.org/10.1007/978-3-031-98668-0_19.
   Enabledness is essential: a stuck instruction is not a terminating run.
   Unlike nextinv', this predicate cannot certify an infinite segment. *)

Require Export Picinae_theory.
From Stdlib Require Import Wellfounded List NArith.
Open Scope N_scope.

Module PicinaeTotal (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL).
Import IL TIL.

Inductive eventually (p:program) (Q:trace -> Prop): trace -> Prop :=
| EventuallyHere t (POST: Q t): eventually p Q t
| EventuallyStep xs t
    (ENABLED: exists xs', can_step p (xs',xs))
    (STEP: forall xs', can_step p (xs',xs) -> eventually p Q (xs'::xs::t)):
    eventually p Q (xs::t).

(* Bind finite segments together, retaining arbitrary trace history. *)
Theorem eventually_bind:
  forall p P Q t, eventually p P t ->
    (forall t', P t' -> eventually p Q t') -> eventually p Q t.
Proof.
  intros p P Q t EV. induction EV; intro CONT.
    apply CONT, POST.
    eapply EventuallyStep. exact ENABLED. intros. apply H; [assumption|exact CONT].
Qed.

(* Existence is accompanied by universal progress in eventually.  This lemma
   exposes an actual finite execution extension for clients needing a witness. *)
Theorem eventually_reaches:
  forall p Q t, eventually p Q t -> exec_prog p t ->
    exists prefix, exec_prog p (prefix++t) /\ Q (prefix++t).
Proof.
  intros p Q t EV. induction EV; intro XP.
    exists nil. split; assumption.
    destruct ENABLED as [xs' CS].
    destruct (H xs' CS) as [prefix [XP' POST]].
      apply exec_prog_step; assumption.
    exists (prefix++xs'::nil). rewrite <- app_assoc. simpl. split; assumption.
Qed.

(* Every continuation path reaches Q after finitely many steps. Together with
   eventually_reaches, this exposes both universal termination and an actual
   execution witness; enabledness prevents vacuous success at stuck states. *)
Theorem eventually_all_paths:
  forall p Q t (EV:eventually p Q t) (run:nat -> trace)
    (START: run 0%nat = t)
    (STEP: forall n, match run n with
      | nil => False
      | xs::hist => exists xs', run (S n) = xs'::xs::hist /\ can_step p (xs',xs)
      end),
  exists n, Q (run n).
Proof.
  intros p Q t EV. induction EV as [t POST|xs hist ENABLED STEP IH];
    intros run START PATH.
    exists 0%nat. rewrite START. exact POST.
    pose proof (PATH 0%nat) as NEXT. rewrite START in NEXT.
    destruct NEXT as [xs' [AT CS]].
    destruct (IH xs' CS (fun n => run (S n))) as [n DONE].
      exact AT.
      intro n. apply PATH.
    exists (S n). exact DONE.
Qed.

Definition exit_post Invs xp (t:trace) := xp t = true /\ true_inv (Invs t).
Definition satisfies_total p Invs xp t := eventually p (exit_post Invs xp) t.

(* Each invariant-to-invariant segment must finish. Its endpoint either exits
   with the postcondition, or satisfies an invariant with strictly smaller rank.
   The rank type and relation are arbitrary, allowing lexicographic measures and
   different phases for sequential loops. No condition is imposed on the rank at
   intermediate instructions. PRE may itself be a finite entry segment. *)
Theorem prove_total_invs:
  forall (A:Type) (R:A -> A -> Prop) (WF: well_founded R)
    p Invs xp (rank:trace -> A) t
    (PRE: eventually p (fun t' => true_inv (Invs t')) t)
    (INV: forall t0, true_inv (Invs t0) ->
      eventually p (fun t' => exit_post Invs xp t' \/
        (true_inv (Invs t') /\ R (rank t') (rank t0))) t0),
  satisfies_total p Invs xp t.
Proof.
  intros A R WF p Invs xp rank t PRE INV.
  assert (FIN: forall r t0, rank t0 = r -> true_inv (Invs t0) ->
    satisfies_total p Invs xp t0).
    intro r. induction (WF r) as [r ACC IH]. intros t0 EQ TRU.
    unfold satisfies_total. eapply eventually_bind. apply INV, TRU.
    intros t' [POST | [TRU' DEC]].
      apply EventuallyHere, POST.
      apply (IH (rank t')). rewrite <- EQ. exact DEC.
        reflexivity. exact TRU'.
  unfold satisfies_total. eapply eventually_bind. exact PRE.
  intros t' TRU. apply (FIN (rank t')); [reflexivity|assumption].
Qed.

(* Carry just the facts needed to reuse a partial-correctness theorem. The
   invariant at a checkpoint need not duplicate its functional specification. *)
Definition execution_context p xp (entry:exit*store) (t:trace) :=
  exec_prog p t /\ ostartof t = Some entry /\ unterminated xp (tl t).

Definition execution_invs p xp entry (checkpoint:trace -> bool) t : option Prop :=
  if checkpoint t then Some (execution_context p xp entry t) else None.

Theorem execution_invs_checkpoint:
  forall p xp entry checkpoint t,
  true_inv (execution_invs p xp entry checkpoint t) -> checkpoint t = true.
Proof.
  intros. unfold execution_invs in H. destruct (checkpoint t).
    reflexivity.
    contradiction.
Qed.

Theorem execution_invs_context:
  forall p xp entry checkpoint t,
  true_inv (execution_invs p xp entry checkpoint t) ->
  execution_context p xp entry t.
Proof.
  intros. unfold execution_invs in H. destruct (checkpoint t); [assumption|contradiction].
Qed.

Lemma ostartof_step:
  forall xs' xs (t:trace), ostartof (xs'::xs::t) = ostartof (xs::t).
Proof. intros. rewrite !ostartof_cons, startof_cons. reflexivity. Qed.

Theorem satall_exit_inv:
  forall p Invs xp t (SA: satisfies_all p Invs xp t)
    (XP: exec_prog p t) (UT: unterminated xp (tl t)) (EX: xp t = true),
  true_inv (Invs t).
Proof.
  intros. specialize (SA XP UT true). inversion SA; subst.
    unfold effinv, effinv' in TRU. rewrite EX in TRU.
    destruct (Invs t); assumption.
    unfold effinv, effinv' in NOI. rewrite EX in NOI.
    destruct (Invs _); discriminate.
Qed.

(* Termination and functional correctness can be established separately, using
   the existing satisfies_all proof verbatim for the latter. *)
Theorem total_of_partial:
  forall p Invs xp entry t
    (PARTIAL: forall t', ostartof t' = Some entry -> satisfies_all p Invs xp t')
    (TERM: eventually p (fun t' => xp t' = true /\
      execution_context p xp entry t') t),
  satisfies_total p Invs xp t.
Proof.
  intros. unfold satisfies_total. eapply eventually_bind. exact TERM.
  intros t' [EX [XP [ORIGIN UT]]]. apply EventuallyHere. split. exact EX.
  eapply satall_exit_inv; [apply PARTIAL| | |]; eassumption.
Qed.

Theorem total_execution_invs:
  forall p Invs xp entry checkpoint t
    (PARTIAL: forall t', ostartof t' = Some entry -> satisfies_all p Invs xp t')
    (TERM: satisfies_total p (execution_invs p xp entry checkpoint) xp t),
  satisfies_total p Invs xp t.
Proof.
  intros. eapply total_of_partial. exact PARTIAL.
  eapply eventually_bind. exact TERM.
  intros t' [EX INV]. apply EventuallyHere. split. exact EX.
  apply execution_invs_context in INV. exact INV.
Qed.

(* Symbolic execution rule, with the same STEP premise as NIStep. *)
Theorem total_step:
  forall p Q a s t sz q
    (IL: p s a = Some (sz,q))
    (ENABLED: exists c' s' x, exec_stmt archtyps s q c' s' x)
    (STEP: forall c' s' x, exec_stmt archtyps s q c' s' x ->
      eventually p Q ((exitof (a+sz) x,reset_temps s s')::(Addr a,s)::t)),
  eventually p Q ((Addr a,s)::t).
Proof.
  intros. eapply EventuallyStep.
    destruct ENABLED as [c' [s' [x XS]]].
    eexists. eapply CanStep; eassumption.
    intros xs' CS. inversion CS; subst.
    rewrite IL in LU. injection LU as SZ EQ. subst. eapply STEP; eassumption.
Qed.

(* Retain execution and first-exit history while symbolically stepping. This
   lets termination proofs reuse satisfies_all for the functional invariant. *)
Theorem total_live_step:
  forall p Q xp a s t sz q
    (IL: p s a = Some (sz,q))
    (LIVE: xp ((Addr a,s)::t) = false)
    (ENABLED: exists c' s' x, exec_stmt archtyps s q c' s' x)
    (STEP: forall c' s' x (XS: exec_stmt archtyps s q c' s' x),
      exec_prog p ((exitof (a+sz) x,reset_temps s s')::(Addr a,s)::t) ->
      unterminated xp ((Addr a,s)::t) ->
      eventually p Q ((exitof (a+sz) x,reset_temps s s')::(Addr a,s)::t))
    (XP: exec_prog p ((Addr a,s)::t)) (UT: unterminated xp t),
  eventually p Q ((Addr a,s)::t).
Proof.
  intros. eapply total_step; [exact IL|exact ENABLED|].
  intros. eapply STEP; [eassumption| |].
    apply exec_prog_step. exact XP. eapply CanStep; eassumption.
    apply unterminated_cons; assumption.
Qed.

Ltac total_here := apply EventuallyHere; cbn [exit_post].
Ltac prove_total measure WF := eapply prove_total_invs with (rank:=measure); [exact WF| |].

Print Assumptions prove_total_invs.

End PicinaeTotal.
