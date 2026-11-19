(* Grok Bot (agent coqettu): satisfies_all_transfer without XPIN.  The callee's
   invariants vanish outside its code (SUP'), so exits of the shared exit
   predicate at other functions' code (e.g. wcscspn's RETs while transferring
   wcsspn) never matter. *)
From Stdlib Require Import Utf8 NArith.
Require Import Picinae_armv8.
Open Scope N.

Section Transfer2.
  Variables (p1 p2: program) (I1 I2: trace -> option Prop) (xp: trace -> bool).
  Hypothesis PS: p1 ⊆2 p2.
  Hypothesis SUP': ∀ a s t, p1 s a = None -> I1 ((Addr a,s)::t) = None.
  Hypothesis AG1: ∀ a s t insn, p1 s a = Some insn -> I2 ((Addr a,s)::t) = I1 ((Addr a,s)::t).
  Hypothesis AG2: ∀ i s t, I2 ((Raise i,s)::t) = I1 ((Raise i,s)::t).
  Hypothesis AG3: I2 nil = I1 nil.

  Theorem nextinv'_transfer2: ∀ b t, nextinv' p1 I1 xp b t -> nextinv' p2 I2 xp b t.
  Proof.
    cofix IH. intros b t NI. inversion NI; subst.
    - apply NIHere'. destruct t as [|[[a|i] s] t].
      + unfold effinv, effexit in *. rewrite AG3. exact TRU.
      + unfold effinv, effexit in *. destruct (xp ((Addr a,s)::t)) eqn:EXIT.
        * destruct (p1 s a) as [insn|] eqn:IL.
          -- rewrite (AG1 _ _ _ _ IL). exact TRU.
          -- rewrite (SUP' _ _ _ IL) in TRU. contradiction.
        * destruct (p1 s a) as [insn|] eqn:IL.
          -- rewrite (AG1 _ _ _ _ IL), (PS _ _ _ IL). exact TRU.
          -- rewrite (SUP' _ _ _ IL) in TRU. contradiction.
      + unfold effinv, effexit in *. rewrite AG2. exact TRU.
    - eapply NIStep'; [|apply PS; exact IL|].
      + unfold effinv, effexit in *. rewrite IL in NOI. rewrite (PS _ _ _ IL), (AG1 _ _ _ _ IL). exact NOI.
      + intros. apply IH. eapply STEP. eassumption.
  Qed.

  Theorem satisfies_all_transfer2: ∀ xs t,
    (∀ xs' t', startof t' xs' = startof t xs -> satisfies_all p1 I1 xp (xs'::t')) ->
    satisfies_all p2 I2 xp (xs::t).
  Proof.
    intros xs t SA.
    assert (RESTRICT: forall t' xs', startof t' xs' = startof t xs ->
              exec_prog p2 (xs'::t') -> unterminated xp t' -> exec_prog p1 (xs'::t')).
    { induction t' as [|xs1 t' IH]; intros xs' START XP UT.
        apply exec_prog_none.
        rewrite startof_cons in START.
        assert (UT1: unterminated xp t') by (eapply unterminated_tl; exact UT).
        assert (XP1: exec_prog p1 (xs1::t')).
          apply IH; [exact START|eapply exec_prog_tail; exact XP|exact UT1].
        assert (NI: nextinv' p1 I1 xp false (xs1::t')) by (apply SA; assumption).
        assert (EXIT: xp (xs1::t') = false) by (inversion UT; assumption).
        assert (CS: can_step p2 (xs',xs1)) by (eapply exec_prog_final; exact XP).
        inversion CS; subst.
        inversion NI; subst.
          unfold effinv, effexit in TRU. rewrite EXIT in TRU.
          destruct (p1 s a) as [insn|] eqn:IL.
            destruct (I1 ((Addr a, s) :: t')); simpl in TRU; contradiction.
            rewrite (SUP' _ _ _ IL) in TRU. contradiction.
          apply exec_prog_step. exact XP1.
          assert (LOOK := PS _ _ _ IL). rewrite LU in LOOK. inversion LOOK; subst.
          eapply CanStep; eassumption.
    }
    intros XP UT b. apply nextinv'_transfer2.
    apply SA; [reflexivity|apply RESTRICT; [reflexivity|exact XP|exact UT]|exact UT].
  Qed.
End Transfer2.
