(* Close independently verified callees against foreign code frontiers. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith.

Definition closed_invs (own:program) (Invs:trace -> option Prop) (t:trace) :=
  match Invs t with
  | Some P => Some P
  | None => match t with (Addr a,s)::_ =>
      match own s a with Some _ => None | None => Some False end
    | _ => None end
  end.

Lemma closed_invs_code : forall own Invs a s t insn,
  own s a=Some insn -> closed_invs own Invs ((Addr a,s)::t)=Invs ((Addr a,s)::t).
Proof. intros own Invs a s t insn IL. unfold closed_invs. destruct (Invs _); [reflexivity|]. rewrite IL. reflexivity. Qed.

Theorem nextinv_closed_pmono : forall p1 p2 Invs xp (PS:p1 ⊆2 p2)
  (SUP:forall a s t,xp ((Addr a,s)::t)=false -> p1 s a=None -> Invs ((Addr a,s)::t)=None)
  b t (NI:nextinv' p1 Invs xp b t),
  nextinv' p2 (closed_invs p1 Invs) xp b t.
Proof.
  intros p1 p2 Invs xp PS SUP. cofix IH. intros b t NI. inversion NI; subst.
  - apply NIHere'. destruct (Invs t) as [P|] eqn:INV.
    + unfold effinv,closed_invs. rewrite INV. unfold effinv,effexit in TRU. unfold effexit.
      rewrite INV in TRU. destruct t as [|[[a|i] s] t]; try exact TRU.
      destruct (xp ((Addr a,s)::t)) eqn:EXIT; [exact TRU|].
      destruct (p1 s a) as [insn|] eqn:IL.
      * rewrite (PS _ _ _ IL). exact TRU.
      * rewrite (SUP _ _ _ EXIT IL) in INV. discriminate.
    + unfold effinv in TRU. rewrite INV in TRU. destruct (effexit _ _ _); contradiction.
  - eapply NIStep'; [|apply PS; exact IL|].
    + unfold effinv in *. rewrite (closed_invs_code _ _ _ _ _ _ IL).
      unfold effexit in *. rewrite IL in NOI. rewrite (PS _ _ _ IL). exact NOI.
    + intros. apply IH. eapply STEP. eassumption.
Qed.

Theorem satisfies_all_closed_pmono : forall p1 p2 Invs xp xs t (PS:p1 ⊆2 p2)
  (SUP:forall a s t,xp ((Addr a,s)::t)=false -> p1 s a=None -> Invs ((Addr a,s)::t)=None)
  (SA:forall xs' t',startof t' xs'=startof t xs -> satisfies_all p1 Invs xp (xs'::t')),
  satisfies_all p2 (closed_invs p1 Invs) xp (xs::t).
Proof.
  intros p1 p2 Invs xp xs t PS SUP SA.
  assert (RESTRICT:forall t' xs',startof t' xs'=startof t xs ->
    exec_prog p2 (xs'::t') -> unterminated xp t' -> exec_prog p1 (xs'::t')).
  { induction t' as [|xs1 t' IH]; intros xs' START XP UT.
    - apply exec_prog_none.
    - rewrite startof_cons in START.
      assert (UT1:unterminated xp t') by (eapply unterminated_tl; exact UT).
      assert (XP1:exec_prog p1 (xs1::t')).
      { apply IH; [exact START|eapply exec_prog_tail; exact XP|exact UT1]. }
      assert (NI:nextinv' p1 Invs xp false (xs1::t')) by (apply SA; assumption).
      assert (EXIT:xp (xs1::t')=false) by (inversion UT; assumption).
      pose proof (exec_prog_final _ _ _ _ XP) as CS. inversion CS; subst.
      inversion NI; subst.
      + unfold effinv,effexit in TRU. rewrite EXIT in TRU.
        destruct (p1 s a) as [insn|] eqn:IL.
        * destruct (Invs _); contradiction.
        * rewrite (SUP _ _ _ EXIT IL) in TRU. contradiction.
      + apply exec_prog_step; [exact XP1|].
        pose proof (PS _ _ _ IL) as LOOK. rewrite LU in LOOK. inversion LOOK; subst.
        eapply CanStep; eassumption. }
  intros XP UT b. apply nextinv_closed_pmono with (p1:=p1); [exact PS|exact SUP|].
  apply SA; [reflexivity|apply RESTRICT; [reflexivity|exact XP|exact UT]|exact UT].
Qed.

Definition code_supported (own:program) (Invs:trace -> option Prop) (xp:trace -> bool) :=
  forall t,(match t with (Addr a,s)::_ => own s a=None | _ => True end) ->
    Invs t=None /\ xp t=false.

Theorem may_call_closed : forall own prog caller Inv cxp xp
  (EXT:own ⊆2 prog) (SUP:code_supported own Inv xp)
  (DIS:forall a s t,own s a<>None -> caller ((Addr a,s)::t)=None /\ cxp ((Addr a,s)::t)=false)
  (HEAD:forall xs t,Inv (xs::t)=Inv (xs::nil))
  (XHEAD:forall xs t,xp (xs::t)=xp (xs::nil)),
  may_call prog caller cxp (closed_invs own Inv) xp.
Proof.
  intros own prog caller Inv cxp xp EXT SUP DIS HEAD XHEAD. repeat split.
  - destruct t as [|[[a|i] s] t].
    + destruct (SUP nil I) as [INV EXIT]. unfold closed_invs,effinv,effexit,effinv_impl.
      rewrite INV,EXIT. destruct (caller nil), (cxp nil); simpl; tauto.
    + destruct (own s a) as [insn|] eqn:IL.
      * destruct (DIS a s t ltac:(rewrite IL; discriminate)) as [CINV CEXIT].
        pose proof (EXT _ _ _ IL) as LOOK.
        unfold effinv,effexit,effinv_impl. rewrite CINV,CEXIT,LOOK.
        destruct (closed_invs own Inv _), (xp _); simpl; tauto.
      * destruct (SUP ((Addr a,s)::t) IL) as [INV EXIT].
        unfold closed_invs,effinv,effexit,effinv_impl. rewrite INV,EXIT,IL.
        destruct (caller _), (cxp _), (prog s a); simpl; tauto.
    + destruct (SUP ((Raise i,s)::t) I) as [INV EXIT].
      unfold closed_invs,effinv,effexit,effinv_impl. rewrite INV,EXIT.
      destruct (caller _), (cxp _); simpl; tauto.
  - destruct t as [|[[a|i] s] t].
    + exact (proj2 (SUP nil I)).
    + destruct (prog s a) as [insn|] eqn:LOOK; [reflexivity|].
      assert (NO:own s a=None).
      { destruct (own s a) as [q|] eqn:IL; [pose proof (EXT _ _ _ IL); congruence|reflexivity]. }
      exact (proj2 (SUP ((Addr a,s)::t) NO)).
    + destruct (SUP ((Raise i,s)::t) I) as [INV EXIT]. unfold closed_invs.
      rewrite INV. exact EXIT.
  - intros xs t. unfold closed_invs. rewrite HEAD. destruct xs as [[a|i] s]; destruct (Inv _); reflexivity.
  - exact XHEAD.
Qed.
