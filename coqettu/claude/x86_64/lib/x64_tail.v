(* Tail calls: a wrapper that JMPs into an independently proved function.

   tail_leaf is call_leaf (x64_compose.v) for a callee whose exits are also
   the caller's exits: the caller has no invariant inside the callee's code
   except at the callee's exits, where it exits too, and the callee's
   postcondition there must imply the caller's.  It is again an instance of
   Picinae's exec_subroutine, with the callee's invariant set closed off
   outside its code (close_invs).

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_compose.
Open Scope N.

Definition post_or_true (o:option Prop) : Prop := match o with Some P => P | None => True end.

Theorem tail_leaf:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None -> xp2 ((Addr a,s)::t) = false ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
    (EXITS: forall a s t, xp2 ((Addr a,s)::t) = true ->
             xp1 ((Addr a,s)::t) = true /\
             (post_or_true (Invs2 ((Addr a,s)::t)) -> true_inv (Invs1 ((Addr a,s)::t))))
    (IH2: forall xs t, Invs2 (xs::t) = Invs2 (xs::nil))
    (XH2: forall xs t, xp2 (xs::t) = xp2 (xs::nil))
    (XC2: forall a s t, xp2 ((Addr a,s)::t) = true -> p1 s a <> None)
    (NIL2: Invs2 nil = None /\ xp2 nil = false)
    (RAISE2: forall i s t, Invs2 ((Raise i,s)::t) = None /\ xp2 ((Raise i,s)::t) = false),
  nextinv' p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof.
  intros. eapply exec_subroutine with (Invs2 := close_invs p1 Invs2) (xp2 := xp2); [|split; [|split]|].
  - intros t xs' START. eapply satisfies_all_pmono_ext; [exact PS|exact SUP| |].
    + intros [|[[a|i] s] t'] H; try reflexivity.
      unfold close_invs. destruct (p1 s a) eqn:IL. reflexivity.
      destruct H as [H|H]. apply XC2 in H. contradiction. contradiction.
    + intros xs'' t'' START'. apply CALLEE. rewrite START'. exact START.
  - intros [|[[a|i] s] t].
    + unfold close_invs. destruct NIL2 as [N1 N2]. simpl. rewrite N1, N2. split; [|reflexivity].
      destruct (Invs1 nil); destruct (xp1 nil); cbv [effinv_impl orb]; tauto.
    + unfold effinv, effexit, close_invs.
      destruct (p1 s a) as [insn|] eqn:IL.
      * rewrite (PS _ _ _ IL).
        destruct (xp2 ((Addr a,s)::t)) eqn:X2.
        -- destruct (EXITS a s t X2) as [X1 IMP]. rewrite X1.
           split; [|reflexivity].
           destruct (Invs2 ((Addr a,s)::t)) as [P2|];
           destruct (Invs1 ((Addr a,s)::t)) as [P1|]; cbv [effinv_impl orb post_or_true true_inv] in *; tauto.
        -- destruct (CALLER a s t) as [I1 X1]. rewrite IL. discriminate. exact X2.
           rewrite I1, X1.
           split; [|reflexivity].
           destruct (Invs2 ((Addr a,s)::t)); cbv [effinv_impl orb]; tauto.
      * split. destruct (Invs1 ((Addr a,s)::t)); destruct (xp1 ((Addr a,s)::t)); destruct (p s a); cbv [effinv_impl orb]; tauto.
        destruct (p s a). reflexivity.
        destruct (xp2 ((Addr a,s)::t)) eqn:X. apply XC2 in X. contradiction. reflexivity.
    + unfold effinv, effexit, close_invs. destruct (RAISE2 i s t) as [R1 R2]. rewrite R1, R2.
      split; [|reflexivity]. destruct (Invs1 ((Raise i,s)::t)); destruct (xp1 ((Raise i,s)::t)); cbv [effinv_impl orb]; tauto.
  - intros [[a|i] s] t; unfold close_invs.
    + rewrite IH2. reflexivity.
    + apply IH2.
  - exact XH2.
  - intros a' s' t2 ENTRY XP UT PRE. apply NIHere'.
    unfold get_postcondition in PRE.
    destruct (xp2 ((Addr a',s')::t2++t1)) eqn:X2; [|destruct PRE].
    destruct (p s' a') eqn:IL; [|destruct PRE].
    destruct (EXITS a' s' (t2++t1) X2) as [X1 IMP].
    unfold effinv, effexit. rewrite X1.
    assert (H: true_inv (Invs1 ((Addr a',s')::t2++t1))).
    { apply IMP. unfold close_invs in PRE.
      destruct (p1 s' a') eqn:IL1.
      - exact PRE.
      - exfalso. exact (XC2 _ _ _ X2 IL1). }
    destruct (Invs1 ((Addr a',s')::t2++t1)); [exact H | destruct H].
Qed.

(* tail_leaf for the exported nextinv. *)
Theorem tail_leaf_ni:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None -> xp2 ((Addr a,s)::t) = false ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
    (EXITS: forall a s t, xp2 ((Addr a,s)::t) = true ->
             xp1 ((Addr a,s)::t) = true /\
             (post_or_true (Invs2 ((Addr a,s)::t)) -> true_inv (Invs1 ((Addr a,s)::t))))
    (IH2: forall xs t, Invs2 (xs::t) = Invs2 (xs::nil))
    (XH2: forall xs t, xp2 (xs::t) = xp2 (xs::nil))
    (XC2: forall a s t, xp2 ((Addr a,s)::t) = true -> p1 s a <> None)
    (NIL2: Invs2 nil = None /\ xp2 nil = false)
    (RAISE2: forall i s t, Invs2 ((Raise i,s)::t) = None /\ xp2 ((Raise i,s)::t) = false),
  nextinv p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof. unfold nextinv. intros. eapply tail_leaf; eassumption. Qed.

(* Generalized composition: the callee's own invariants may be used to rule
   out caller invariants and exits inside its code.  This is needed when the
   caller's exit condition depends on the store: e.g. wcscspn tail-calls
   wcslen, so wcslen's RET is wcscspn's exit when RSP is wcscspn's entry RSP,
   but the same RET is also an internal point of wcscspn's callee wcschr
   (which calls wcslen), where wcschr's invariant puts RSP lower.

   inv_or_noexit (Invs1 t) (xp1 t) says what the caller requires at a callee
   exit: the caller's invariant if it has one, else that it does not exit. *)
Definition inv_or_noexit (o:option Prop) (x:bool) : Prop :=
  match o with Some P => P | None => x = false end.

Theorem call_leaf_g:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None -> xp2 ((Addr a,s)::t) = false ->
             post_or_true (Invs2 ((Addr a,s)::t)) ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
    (EXITS: forall a s t, xp2 ((Addr a,s)::t) = true -> post_or_true (Invs2 ((Addr a,s)::t)) ->
             inv_or_noexit (Invs1 ((Addr a,s)::t)) (xp1 ((Addr a,s)::t)))
    (IH2: forall xs t, Invs2 (xs::t) = Invs2 (xs::nil))
    (XH2: forall xs t, xp2 (xs::t) = xp2 (xs::nil))
    (XC2: forall a s t, xp2 ((Addr a,s)::t) = true -> p1 s a <> None)
    (NIL2: Invs2 nil = None /\ xp2 nil = false)
    (RAISE2: forall i s t, Invs2 ((Raise i,s)::t) = None /\ xp2 ((Raise i,s)::t) = false)
    (POST: forall a' s' t2
             (ENTRY: startof t2 (Addr a', s') = (Addr a1, s1))
             (XP: exec_prog p ((Addr a',s')::t2))
             (UT: unterminated xp2 t2)
             (PRE: true_inv (get_postcondition p (close_invs p1 Invs2) xp2 a' s' (t2++t1))),
           nextinv' p Invs1 xp1 true ((Addr a',s')::t2++t1)),
  nextinv' p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof.
  intros. eapply exec_subroutine; [|split; [|split]|exact POST].
  - intros t xs' START. eapply satisfies_all_pmono_ext; [exact PS|exact SUP| |].
    + intros [|[[a|i] s] t'] H; try reflexivity.
      unfold close_invs. destruct (p1 s a) eqn:IL. reflexivity.
      destruct H as [H|H]. apply XC2 in H. contradiction. contradiction.
    + intros xs'' t'' START'. apply CALLEE. rewrite START'. exact START.
  - intros [|[[a|i] s] t].
    + unfold close_invs. destruct NIL2 as [N1 N2]. simpl. rewrite N1, N2. split; [|reflexivity].
      destruct (Invs1 nil); destruct (xp1 nil); cbv [effinv_impl orb]; tauto.
    + unfold effinv, effexit, close_invs.
      destruct (p1 s a) as [insn|] eqn:IL.
      * rewrite (PS _ _ _ IL).
        assert (NN: p1 s a <> None) by (rewrite IL; discriminate).
        destruct (xp2 ((Addr a,s)::t)) eqn:X2.
        -- pose proof (EXITS a s t X2) as E. split; [|reflexivity].
           destruct (Invs2 ((Addr a,s)::t)) as [Q|];
           destruct (Invs1 ((Addr a,s)::t)) as [P|];
           destruct (xp1 ((Addr a,s)::t));
           cbv [effinv_impl orb post_or_true inv_or_noexit] in *; try tauto;
           intro HQ; specialize (E HQ); discriminate E.
        -- pose proof (CALLER a s t NN X2) as E. split; [|reflexivity].
           destruct (Invs2 ((Addr a,s)::t)) as [Q|].
           ++ destruct (Invs1 ((Addr a,s)::t)) as [P|] eqn:I1;
              destruct (xp1 ((Addr a,s)::t)) eqn:X1;
              cbv [effinv_impl orb post_or_true] in *; try tauto;
              intro HQ; destruct (E HQ) as [A B]; discriminate.
           ++ destruct (E I) as [A B]. rewrite A, B. exact I.
      * split. destruct (Invs1 ((Addr a,s)::t)); destruct (xp1 ((Addr a,s)::t)); destruct (p s a); cbv [effinv_impl orb]; tauto.
        destruct (p s a). reflexivity.
        destruct (xp2 ((Addr a,s)::t)) eqn:X. apply XC2 in X. contradiction. reflexivity.
    + unfold effinv, effexit, close_invs. destruct (RAISE2 i s t) as [R1 R2]. rewrite R1, R2.
      split; [|reflexivity]. destruct (Invs1 ((Raise i,s)::t)); destruct (xp1 ((Raise i,s)::t)); cbv [effinv_impl orb]; tauto.
  - intros [[a|i] s] t; unfold close_invs.
    + rewrite IH2. reflexivity.
    + apply IH2.
  - exact XH2.
Qed.

Theorem call_leaf_g_ni:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None -> xp2 ((Addr a,s)::t) = false ->
             post_or_true (Invs2 ((Addr a,s)::t)) ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
    (EXITS: forall a s t, xp2 ((Addr a,s)::t) = true -> post_or_true (Invs2 ((Addr a,s)::t)) ->
             inv_or_noexit (Invs1 ((Addr a,s)::t)) (xp1 ((Addr a,s)::t)))
    (IH2: forall xs t, Invs2 (xs::t) = Invs2 (xs::nil))
    (XH2: forall xs t, xp2 (xs::t) = xp2 (xs::nil))
    (XC2: forall a s t, xp2 ((Addr a,s)::t) = true -> p1 s a <> None)
    (NIL2: Invs2 nil = None /\ xp2 nil = false)
    (RAISE2: forall i s t, Invs2 ((Raise i,s)::t) = None /\ xp2 ((Raise i,s)::t) = false)
    (POST: forall a' s' t2
             (ENTRY: startof t2 (Addr a', s') = (Addr a1, s1))
             (UT: unterminated xp2 t2)
             (PRE: true_inv (get_postcondition p (close_invs p1 Invs2) xp2 a' s' (t2++t1))),
           nextinv p Invs1 xp1 true ((Addr a',s')::t2++t1)),
  nextinv p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof.
  unfold nextinv. intros. eapply call_leaf_g; try eassumption.
  intros. apply POST; try assumption. rewrite app_comm_cons. apply exec_prog_app.
    eapply exec_prog_tail. eassumption.
    destruct t1. exact I. simpl. rewrite ENTRY. eapply exec_prog_final. eassumption.
    assumption.
Qed.

(* Jump into a callee whose exits land on caller invariants: a tail call
   (the caller exits there, possibly depending on the store), or a call whose
   return point the caller cuts at (the callee's RET).  The callee's
   postcondition must establish the caller's invariant there. *)
Theorem tail_leaf_g_ni:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None -> xp2 ((Addr a,s)::t) = false ->
             post_or_true (Invs2 ((Addr a,s)::t)) ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
    (EXITS: forall a s t, xp2 ((Addr a,s)::t) = true -> post_or_true (Invs2 ((Addr a,s)::t)) ->
             true_inv (Invs1 ((Addr a,s)::t)))
    (IH2: forall xs t, Invs2 (xs::t) = Invs2 (xs::nil))
    (XH2: forall xs t, xp2 (xs::t) = xp2 (xs::nil))
    (XC2: forall a s t, xp2 ((Addr a,s)::t) = true -> p1 s a <> None)
    (NIL2: Invs2 nil = None /\ xp2 nil = false)
    (RAISE2: forall i s t, Invs2 ((Raise i,s)::t) = None /\ xp2 ((Raise i,s)::t) = false),
  nextinv p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof.
  unfold nextinv. intros. eapply call_leaf_g; try eassumption.
  - intros a s t X2 H. pose proof (EXITS a s t X2 H) as T.
    unfold inv_or_noexit. destruct (Invs1 ((Addr a,s)::t)). exact T. destruct T.
  - intros a' s' t2 ENTRY XP' UT PRE. apply NIHere'.
    unfold get_postcondition in PRE.
    destruct (xp2 ((Addr a',s')::t2++t1)) eqn:X2; [|destruct PRE].
    destruct (p s' a') eqn:IL; [|destruct PRE].
    assert (H2: post_or_true (Invs2 ((Addr a',s')::t2++t1))).
    { unfold close_invs in PRE. destruct (p1 s' a') eqn:IL1.
      - destruct (Invs2 _); exact PRE.
      - exfalso. exact (XC2 _ _ _ X2 IL1). }
    pose proof (EXITS a' s' (t2++t1) X2 H2) as T.
    unfold effinv. simpl orb.
    destruct (Invs1 ((Addr a',s')::t2++t1)); [exact T | destruct T].
Qed.
