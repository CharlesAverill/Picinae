(* Composing independently proved function contracts.

   A leaf contract proved as   satisfies_all prog (f_invs ...) f_exit
   has invariants only at f's own addresses.  To call f from a caller g with
   Picinae's exec_subroutine, the callee's invariant set must imply the
   caller's at every point (may_call); in particular it must say False at
   g's invariant points.  satisfies_all_pmono_ext shows that a contract can be
   transported to a larger program AND have its invariants outside f's code
   replaced by anything (e.g. False): before its exit, f's execution never
   leaves f's code, because Picinae's effective invariant (effinv) already
   demands False at any non-code address that is not an exit.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Open Scope N.

(* Invs' agrees with Invs wherever the trace is at an exit or in p1's code
   (and at exceptions). *)
Definition invs_agree (p1:program) (Invs Invs':trace -> option Prop) (xp:trace -> bool) :=
  forall t, match t with
            | (Addr a,s)::_ => xp t = true \/ p1 s a <> None
            | _ => True end -> Invs' t = Invs t.

Theorem nextinv'_pmono_ext:
  forall p1 p2 Invs Invs' xp (PS: p1 ⊆2 p2)
    (SUP: forall a s t, xp ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs ((Addr a,s)::t) = None)
    (AG: invs_agree p1 Invs Invs' xp)
    b t (NI: nextinv' p1 Invs xp b t),
  nextinv' p2 Invs' xp b t.
Proof.
  intros p1 p2 Invs Invs' xp PS SUP AG. cofix IH. intros b t NI. inversion NI; subst.
  - apply NIHere'. unfold effinv, effexit in *.
    destruct t as [|[[a|i] s] t].
    + rewrite (AG nil I). exact TRU.
    + destruct (xp ((Addr a,s)::t)) eqn:EXIT.
      * rewrite (AG ((Addr a,s)::t)) by (left; exact EXIT). exact TRU.
      * destruct (p1 s a) as [insn|] eqn:IL.
        -- rewrite (AG ((Addr a,s)::t)) by (right; rewrite IL; discriminate).
           rewrite (PS _ _ _ IL). exact TRU.
        -- rewrite (SUP _ _ _ EXIT IL) in TRU. contradiction.
    + rewrite (AG ((Raise i,s)::t) I). exact TRU.
  - eapply NIStep'; [|apply PS; exact IL|].
    + unfold effinv, effexit in *. rewrite IL in NOI. rewrite (PS _ _ _ IL).
      rewrite AG by (right; rewrite IL; discriminate). exact NOI.
    + intros. apply IH. eapply STEP. eassumption.
Qed.

Theorem satisfies_all_pmono_ext:
  forall p1 p2 Invs Invs' xp xs t (PS: p1 ⊆2 p2)
    (SUP: forall a s t, xp ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs ((Addr a,s)::t) = None)
    (AG: invs_agree p1 Invs Invs' xp)
    (SA: forall xs' t', startof t' xs' = startof t xs ->
         satisfies_all p1 Invs xp (xs'::t')),
  satisfies_all p2 Invs' xp (xs::t).
Proof.
  intros p1 p2 Invs Invs' xp xs t PS SUP AG SA.
  assert (RESTRICT: forall t' xs', startof t' xs' = startof t xs ->
            exec_prog p2 (xs'::t') -> unterminated xp t' -> exec_prog p1 (xs'::t')).
  { induction t' as [|xs1 t' IH]; intros xs' START XP UT.
      apply exec_prog_none.
      rewrite startof_cons in START.
      assert (UT1: unterminated xp t') by (eapply unterminated_tl; exact UT).
      assert (XP1: exec_prog p1 (xs1::t')).
        apply IH; [exact START|eapply exec_prog_tail; exact XP|exact UT1].
      assert (NI: nextinv' p1 Invs xp false (xs1::t')) by (apply SA; assumption).
      assert (EXIT: xp (xs1::t') = false) by (inversion UT; assumption).
      assert (CS: can_step p2 (xs',xs1)) by (eapply exec_prog_final; exact XP).
      inversion CS; subst.
      inversion NI; subst.
        unfold effinv, effexit in TRU. rewrite EXIT in TRU.
        destruct (p1 s a) as [insn|] eqn:IL.
          destruct (Invs _); contradiction.
          rewrite (SUP _ _ _ EXIT IL) in TRU. contradiction.
        apply exec_prog_step. exact XP1.
        assert (LOOK := PS _ _ _ IL). rewrite LU in LOOK. inversion LOOK; subst.
        eapply CanStep; eassumption.
  }
  intros XP UT b. eapply nextinv'_pmono_ext; [exact PS|exact SUP|exact AG|].
  apply SA; [reflexivity|apply RESTRICT; [reflexivity|exact XP|exact UT]|exact UT].
Qed.

(* The callee's invariant set, closed off: False at every point outside the
   callee's code p1. *)
Definition close_invs (p1:program) (Invs:trace -> option Prop) (t:trace) : option Prop :=
  match t with
  | (Addr a,s)::_ => if p1 s a then Invs t else Some False
  | _ => Invs t
  end.

(* Call a leaf function whose contract (Invs2, xp2) was proved for its own code
   p1 (and hence, by satisfies_all_pmono_ext, for any larger program p).
   Side conditions: the caller has no invariant and no exit inside p1; the
   callee's invariants and exits depend only on the head of the trace, its
   exits are inside its code, and it has no invariant at exceptions. *)
Theorem call_leaf:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
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
      * destruct (CALLER a s t) as [I1 X1]. rewrite IL. discriminate.
        rewrite I1, X1, (PS _ _ _ IL).
        split. destruct (Invs2 ((Addr a,s)::t)); destruct (xp2 ((Addr a,s)::t)); cbv [effinv_impl orb]; tauto. reflexivity.
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

(* call_leaf for the exported nextinv (which carries the exec_prog premise),
   in the shape of Picinae's perform_call. *)
Theorem call_leaf_ni:
  forall p p1 Invs1 xp1 Invs2 xp2 a1 s1 t1
    (PS: p1 ⊆2 p)
    (SUP: forall a s t, xp2 ((Addr a,s)::t) = false -> p1 s a = None ->
          Invs2 ((Addr a,s)::t) = None)
    (CALLEE: forall t xs', startof t xs' = (Addr a1, s1) ->
             satisfies_all p1 Invs2 xp2 (xs'::t))
    (CALLER: forall a s t, p1 s a <> None ->
             Invs1 ((Addr a,s)::t) = None /\ xp1 ((Addr a,s)::t) = false)
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
  unfold nextinv. intros. eapply call_leaf; try eassumption.
  intros. apply POST; try assumption. rewrite app_comm_cons. apply exec_prog_app.
    eapply exec_prog_tail. eassumption.
    destruct t1. exact I. simpl. rewrite ENTRY. eapply exec_prog_final. eassumption.
    assumption.
Qed.

(* Decide a match on a concrete address by walking the bits of a. *)
Ltac addr_cases H :=
  repeat first
  [ discriminate H
  | match type of H with context [match ?n with _ => _ end] => destruct n end ].

(* A store of 8 bytes at rsp - k (8 <= k <= F) leaves every byte outside the
   F bytes below rsp unchanged. *)
Lemma stack_store_frame:
  forall m rsp k v b F, 8 <= k <= F -> F < 2^63 -> F <= msub 64 b (msub 64 rsp F) ->
  (setmem 64 LittleE 8 m (msub 64 rsp k) v) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp k v b F K FB B. apply getmem_noverlap. intros [x [y [X [Y E]]]].
  unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* "m' agrees with m outside the F bytes below rsp" *)
Definition stack_frame (m m' rsp F:N) :=
  forall b, F <= msub 64 b (msub 64 rsp F) -> m' Ⓑ[b] = m Ⓑ[b].

Lemma stack_frame_refl: forall m rsp F, stack_frame m m rsp F.
Proof. intros m rsp F b _. reflexivity. Qed.

Lemma stack_frame_store:
  forall m m' rsp F k v, 8 <= k <= F -> F < 2^63 -> stack_frame m m' rsp F ->
  stack_frame m (setmem 64 LittleE 8 m' (msub 64 rsp k) v) rsp F.
Proof.
  intros m m' rsp F k v K FB SF b B. rewrite (stack_store_frame m' rsp k v b F) by assumption.
  apply SF, B.
Qed.

(* A union of two programs is contained in any program containing both. *)
Lemma updateall2_lub {A B C}:
  forall (f g h: A -> B -> option C), f ⊆2 h -> g ⊆2 h -> updateall2 f g ⊆2 h.
Proof.
  intros f g h F G. rewrite <- (updateall2_subset g h G). apply updateall2_mono. exact F.
Qed.

(* An 8-byte read entirely above the stack frame sees the old memory. *)
Lemma stack_frame_get8:
  forall m m' rsp F a, stack_frame m m' rsp F -> F < 2^63 ->
  F <= msub 64 a (msub 64 rsp F) <= 2^64 - 8 ->
  m' Ⓠ[a] = m Ⓠ[a].
Proof.
  intros m m' rsp F a SF FB A. apply getmem_frame_mem. intros a' A'.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF.
  unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma stack_frame_trans:
  forall m1 m2 m3 rsp1 F1 rsp2 F2,
  stack_frame m1 m2 rsp1 F1 -> stack_frame m2 m3 rsp2 F2 ->
  forall rsp F, (forall b, F <= msub 64 b (msub 64 rsp F) ->
                 F1 <= msub 64 b (msub 64 rsp1 F1) /\ F2 <= msub 64 b (msub 64 rsp2 F2)) ->
  stack_frame m1 m3 rsp F.
Proof.
  intros m1 m2 m3 rsp1 F1 rsp2 F2 S1 S2 rsp F H b B. destruct (H b B) as [B1 B2].
  rewrite S2 by exact B2. apply S1, B1.
Qed.
