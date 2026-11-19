(* Grok Bot (agent coqettu): changing the exit predicate of a proof.
   An exit predicate only matters at trace heads inside the program: outside
   it every trace already counts as exited.  So a satisfies_all proof for
   exits xp1 is one for any xp2 agreeing with xp1 on heads in the program's
   code.  With GrokWeaken and satisfies_all_transfer' (no XPIN), this places a
   callee into a caller family whose level also holds other callees' exits
   (wcsspn and wcscspn inside wcstok). *)
From Stdlib Require Import Utf8 NArith List.
Require Import Picinae_armv8.
Open Scope N.

Section Exits.
  Variables (p: program) (I: trace -> option Prop) (xp1 xp2: trace -> bool).
  Hypothesis XA: ∀ a s t insn, p s a = Some insn -> xp2 ((Addr a,s)::t) = xp1 ((Addr a,s)::t).
  Hypothesis XN: xp2 nil = xp1 nil.

  Lemma effinv_xa: ∀ b t, effinv b p I xp2 t = effinv b p I xp1 t.
  Proof.
    intros b [|[[a|i] s] t]; unfold effinv, effexit.
    - rewrite XN. reflexivity.
    - destruct (p s a) eqn:IL.
      + rewrite (XA _ _ _ _ IL). reflexivity.
      + destruct (xp1 ((Addr a,s)::t)), (xp2 ((Addr a,s)::t)); reflexivity.
    - destruct (xp1 ((Raise i,s)::t)), (xp2 ((Raise i,s)::t)); reflexivity.
  Qed.

  Theorem nextinv'_xa: ∀ b t, nextinv' p I xp1 b t -> nextinv' p I xp2 b t.
  Proof.
    cofix IH. intros b t NI. inversion NI; subst.
    - apply NIHere'. rewrite effinv_xa. exact TRU.
    - eapply NIStep'; [rewrite effinv_xa; exact NOI | exact IL |].
      intros. apply IH. eapply STEP. eassumption.
  Qed.

  Lemma unterminated_xa: ∀ t xs, exec_prog p (xs::t) -> unterminated xp2 t -> unterminated xp1 t.
  Proof.
    induction t as [|xs1 t IH]; intros xs XP UT.
    - inversion UT; subst. constructor. rewrite <- XN. assumption.
    - inversion UT; subst. constructor.
      + assert (CS: can_step p (xs,xs1)) by (eapply exec_prog_final; exact XP).
        inversion CS; subst. rewrite <- (XA _ _ _ _ LU). assumption.
      + eapply IH; [eapply exec_prog_tail; exact XP | assumption].
  Qed.

  Theorem satisfies_all_xa: ∀ t, satisfies_all p I xp1 t -> satisfies_all p I xp2 t.
  Proof.
    intros [|xs t] SA XP UT b; apply nextinv'_xa, SA; try assumption.
    - inversion UT; subst. constructor. rewrite <- XN. assumption.
    - eapply unterminated_xa; eassumption.
  Qed.
End Exits.
