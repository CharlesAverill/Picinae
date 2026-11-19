(* GrokTail: reusing a callee's partial-correctness theorem for a function
   that is a single unconditional tail branch to it (Grok Bot / coqettu).

   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith List.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

Section TailCall.
  Variable p : program.
  Variable Invs : trace -> option Prop.
  Variable xp : trace -> bool.
  (* invariants and exits depend only on the newest trace element
     (true of make_invs / make_exits) *)
  Hypothesis HI : ∀ x t1 t2, Invs (x::t1) = Invs (x::t2).
  Hypothesis HX : ∀ x t1 t2, xp (x::t1) = xp (x::t2).
  Hypothesis XNIL : xp nil = false.

  Lemma effinv_retail: ∀ b x t1 t2, effinv b p Invs xp (x::t1) = effinv b p Invs xp (x::t2).
  Proof.
    intros. unfold effinv, effexit. rewrite (HI x t1 t2), (HX x t1 t2). reflexivity.
  Qed.

  Lemma nextinv'_retail: ∀ b x t1 t2, nextinv' p Invs xp b (x::t1) -> nextinv' p Invs xp b (x::t2).
  Proof.
    cofix CIH. intros b x t1 t2 H. inversion H; subst.
    - apply NIHere'. rewrite <- (effinv_retail b x t1 t2). exact TRU.
    - eapply NIStep'.
      + rewrite <- (effinv_retail b (Addr a, s) t1 t2). exact NOI.
      + exact IL.
      + intros c1 s1 x1 XS. exact (CIH _ _ _ _ (STEP c1 s1 x1 XS)).
  Qed.

  Lemma unterminated_untail: ∀ l x0, unterminated xp (l ++ x0::nil) -> unterminated xp l.
  Proof.
    induction l; intros x0 UT.
    - apply ForallPrefixes_nil. exact XNIL.
    - inversion UT; subst. apply ForallPrefixes_cons.
      + rewrite (HX a l (l ++ x0::nil)). assumption.
      + eapply IHl. eassumption.
  Qed.

  Variables (a0 a1 : addr).
  Hypothesis NOI0 : ∀ s t, Invs ((Addr a0, s)::t) = None.
  Hypothesis NOX0 : ∀ s t, xp ((Addr a0, s)::t) = false.
  Hypothesis JMP : ∀ s, p s a0 = Some (4, Jmp (Word a1 64)).
  Variable P : store -> Prop.
  Hypothesis PEXT : ∀ s s', (∀ v, s v = s' v) -> P s -> P s'.
  Hypothesis TGT : ∀ s t xs', startof t xs' = (Addr a1, s) -> P s -> satisfies_all p Invs xp (xs'::t).

  Lemma jmp_step: ∀ s c1 s1 x1, exec_stmt archtyps s (Jmp (Word a1 64)) c1 s1 x1 ->
    x1 = Some (Addr a1) /\ (∀ v, s v = reset_temps s s1 v).
  Proof.
    intros s c1 s1 x1 XS. inversion XS; subst. inversion E; subst. split. reflexivity.
    intro v. unfold reset_temps, reset_vars. destruct (archtyps v); reflexivity.
  Qed.

  Theorem tailcall_satisfies_all:
    ∀ s t xs', startof t xs' = (Addr a0, s) -> P s -> satisfies_all p Invs xp (xs'::t).
  Proof.
    intros s t xs' START PS XP UT b.
    destruct t as [|y t].
    - (* the trace is just the entry state: one step reaches the target *)
      cbn in START. subst xs'.
      eapply NIStep'.
      + unfold effinv, effexit. rewrite NOI0, NOX0, JMP. destruct b; reflexivity.
      + apply JMP.
      + intros c1 s1 x1 XS. destruct (jmp_step _ _ _ _ XS) as [-> EQ].
        cbn [exitof].
        apply (nextinv'_retail true _ nil).
        apply (TGT (reset_temps s s1) nil); [reflexivity | exact (PEXT _ _ EQ PS) | apply exec_prog_none | apply ForallPrefixes_nil, XNIL].
    - (* split off the entry state *)
      assert (TL: y::t = removelast (y::t) ++ (Addr a0, s)::nil).
      { rewrite <- START. unfold startof. cbn [last].
        rewrite (@app_removelast_last _ (y::t) xs' ltac:(discriminate)) at 1.
        destruct t; reflexivity. }
      set (T1 := xs' :: removelast (y::t)).
      assert (ET: xs'::y::t = T1 ++ (Addr a0, s)::nil) by (unfold T1; rewrite TL at 1; reflexivity).
      rewrite ET in XP. apply exec_prog_split in XP. destruct XP as (_ & CS & XP1).
      unfold can_step_between in CS. cbn [ostartof] in CS.
      inversion CS; subst. rewrite JMP in LU. inversion LU; subst.
      destruct (jmp_step _ _ _ _ XS) as [-> EQ].
      assert (UT1: unterminated xp (tl T1)).
      { cbn [tl] in UT. unfold T1. cbn [tl]. rewrite TL in UT. eapply unterminated_untail. exact UT. }
      assert (SA: satisfies_all p Invs xp T1).
      { unfold T1. apply (TGT (reset_temps s s')).
        - cbn [exitof] in *. first [ (symmetry; exact H0) | exact H0 | (cbn [removelast] in *; symmetry; exact H0) | (unfold startof in *; cbn [removelast] in *; symmetry; exact H0) ].
        - exact (PEXT _ _ EQ PS). }
      specialize (SA XP1 UT1 b).
      rewrite ET. unfold T1 in SA |- *. cbn [app]. exact (nextinv'_retail b xs' _ _ SA).
  Qed.
End TailCall.

(* One instruction at a0 that always continues to a1, followed by anything
   proved from a1: peels a short straight-line prefix (e.g. bzero: mov, mov,
   then b memset) off a tail call. *)
Section StepThen.
  Variable p : program.
  Variable Invs : trace -> option Prop.
  Variable xp : trace -> bool.
  Hypothesis HI : ∀ x t1 t2, Invs (x::t1) = Invs (x::t2).
  Hypothesis HX : ∀ x t1 t2, xp (x::t1) = xp (x::t2).
  Hypothesis XNIL : xp nil = false.
  Variables (a0 a1 : addr) (sz : N) (q : stmt).
  Hypothesis NOI0 : ∀ s t, Invs ((Addr a0, s)::t) = None.
  Hypothesis NOX0 : ∀ s t, xp ((Addr a0, s)::t) = false.
  Hypothesis STMT : ∀ s, p s a0 = Some (sz, q).
  Variables P Q : store -> Prop.
  Hypothesis STEP : ∀ s c1 s1 x1, P s -> exec_stmt archtyps s q c1 s1 x1 ->
    exitof (a0 + sz) x1 = Addr a1 /\ Q (reset_temps s s1).
  Hypothesis TGT : ∀ s t xs', startof t xs' = (Addr a1, s) -> Q s -> satisfies_all p Invs xp (xs'::t).

  Theorem step_satisfies_all:
    ∀ s t xs', startof t xs' = (Addr a0, s) -> P s -> satisfies_all p Invs xp (xs'::t).
  Proof.
    intros s t xs' START PS XP UT b.
    destruct t as [|y t].
    - cbn in START. subst xs'.
      eapply NIStep'.
      + unfold effinv, effexit. rewrite NOI0, NOX0, STMT. destruct b; reflexivity.
      + apply STMT.
      + intros c1 s1 x1 XS. destruct (STEP _ _ _ _ PS XS) as [EX QS]. rewrite EX.
        apply (nextinv'_retail p Invs xp HI HX true _ nil).
        apply (TGT (reset_temps s s1) nil); [reflexivity | exact QS | apply exec_prog_none | apply ForallPrefixes_nil, XNIL].
    - assert (TL: y::t = removelast (y::t) ++ (Addr a0, s)::nil).
      { rewrite <- START. unfold startof. cbn [last].
        rewrite (@app_removelast_last _ (y::t) xs' ltac:(discriminate)) at 1.
        destruct t; reflexivity. }
      set (T1 := xs' :: removelast (y::t)).
      assert (ET: xs'::y::t = T1 ++ (Addr a0, s)::nil) by (unfold T1; rewrite TL at 1; reflexivity).
      rewrite ET in XP. apply exec_prog_split in XP. destruct XP as (_ & CS & XP1).
      unfold can_step_between in CS. cbn [ostartof] in CS.
      inversion CS; subst. rewrite STMT in LU. inversion LU; subst.
      destruct (STEP _ _ _ _ PS XS) as [EX QS].
      assert (UT1: unterminated xp (tl T1)).
      { cbn [tl] in UT. unfold T1. cbn [tl]. rewrite TL in UT. eapply (unterminated_untail xp HX XNIL). exact UT. }
      assert (SA: satisfies_all p Invs xp T1).
      { unfold T1. apply (TGT (reset_temps s s')).
        - rewrite EX in *. cbn [exitof] in *. first [ (symmetry; exact H0) | exact H0 | (cbn [removelast] in *; symmetry; exact H0) | (unfold startof in *; cbn [removelast] in *; symmetry; exact H0) ].
        - exact QS. }
      specialize (SA XP1 UT1 b).
      rewrite ET. unfold T1 in SA |- *. cbn [app]. exact (nextinv'_retail p Invs xp HI HX b xs' _ _ SA).
  Qed.
End StepThen.

(* reading a register after a Move, through reset_temps *)
Lemma reset_move: ∀ (s:store) v u w v', archtyps v = Some w ->
  reset_temps s (s[v := u]) v' = (s[v := u]) v'.
Proof.
  intros s v u w v' T. unfold reset_temps, reset_vars.
  destruct (archtyps v') eqn:E. reflexivity.
  rewrite update_frame. reflexivity. intro H. subst. congruence.
Qed.
