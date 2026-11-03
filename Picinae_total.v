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

Ltac total_here := apply EventuallyHere; cbn [exit_post].
Ltac prove_total rank WF := eapply prove_total_invs with (rank:=rank); [exact WF| |].

Print Assumptions prove_total_invs.

End PicinaeTotal.
