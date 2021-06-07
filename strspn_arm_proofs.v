Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import PArith.
Require Import Picinae_armv7.
Require Import strspn_arm.

Import ARMNotations.
Open Scope N.
Open Scope list_scope.
Import List.ListNotations.
Import List.

Definition fh := htotal.

Theorem strspn_nwc: forall s2 s1, strspn_arm s1 = strspn_arm s2.
Proof. reflexivity. Qed.

Theorem strspn_welltyped: welltyped_prog armtypctx strspn_arm.
Proof.
  Picinae_typecheck.
Qed.

Print list.

Fixpoint cstring m loc s :=
  match s with
  | [] => m Ⓑ[loc] = 0
  | x :: xs => x <> 0 /\ m Ⓑ[loc] = x /\ cstring m (loc⊕1) xs
  end.

(* Inductive cstring : (addr -> N) -> addr -> list N -> Prop := *)
(* | CStrNil m loc : m Ⓑ[loc] = 0 -> cstring m loc [] *)
(* | CStrCons m loc x xs : *)
(*     m Ⓑ[loc] <> 0 -> m Ⓑ[loc] = x -> *)
(*     cstring m (loc+1) xs -> cstring m loc (x::xs). *)

(* Definition cstring m loc s := *)
(*   m Ⓑ[loc ⊕ N.of_nat (length s)] = 0 /\ *)
(*   ~In 0 s /\ *)
(*   forall n, (n < length s)%nat -> m Ⓑ[loc ⊕ N.of_nat n] = nth n s 0. *)

Definition strspn_post strloc acceptloc accept m (_ : exit) s :=
  exists answer,
    (* s V_MEM32 = Ⓜm /\ *)
    (* s R_R0 = Ⓓstr /\ *)
    (* s R_R1 = Ⓓacceptloc /\ *)
    s R_R0 = Ⓓanswer /\
    cstring m acceptloc accept /\
    (forall n, n < answer -> In (m Ⓑ[strloc ⊕ n]) accept) /\
    ~In (m Ⓑ[strloc ⊕ answer]) accept.

Definition strspn_invs strloc acceptloc accept m a s :=
  (* let common n m := *)
  (*     s R_R0 = n /\ *)
  (*     s R_R1 = acceptloc /\ *)
  (*     s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\ *)
  (*     s R_R12 = Ⓓ(m Ⓑ[strloc+n]) /\ *)
  (*     s R_LR = Ⓓ(strloc+n) *)
  match a with
  | 16 =>
    Some (s R_R0 = Ⓓstrloc /\ s R_R1 = Ⓓacceptloc /\ s V_MEM32 = Ⓜm /\
          s R_R12 = Ⓓm Ⓑ[strloc])
  | 28 =>
    Some
      (exists strind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓacceptloc /\
          s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\
          s R_R12 = Ⓓ(m Ⓑ[strloc⊕strind]) /\
          s R_LR = Ⓓ(strloc⊕strind) /\
          cstring m acceptloc accept /\
          forall i, i < strind -> In (m Ⓑ[strloc⊕i]) accept)
  | 60 =>
    Some
      (exists strind acceptind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓacceptloc /\
          s R_R2 = Ⓓ(acceptloc⊕acceptind) /\
          (* s R_R3 = Ⓓ(m Ⓑ[acceptloc⊕acceptind]) /\ *)
          s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\
          s R_R12 = Ⓓ(m Ⓑ[strloc⊕strind]) /\
          s R_LR = Ⓓ(strloc⊕strind) /\
          cstring m acceptloc accept /\
          (forall i, i < strind -> In (m Ⓑ[strloc⊕i]) accept) /\
          (forall i, i < acceptind ->
                     m Ⓑ[strloc⊕strind] <> m Ⓑ[acceptloc⊕i]))
  | _ => None
  end.

Definition strspn_invset strloc acceptloc accept m :=
  invs (strspn_invs strloc acceptloc accept m)
       (strspn_post strloc acceptloc accept m).

Theorem un_d_ify x y : Ⓓx = Ⓓy -> x = y.
  intro H.
  inversion H.
  reflexivity.
Qed.

Theorem mod_sub_eq w n m :
  n < 2^w -> m < 2^w -> 2 ^ w + n ⊖ m = 0 -> n = m.
Admitted.

Theorem substr_accept_addone m strloc strind accept :
  In (m Ⓑ[ strloc ⊕ strind ]) accept ->
  (forall n, n < strind -> In (m Ⓑ[ strloc ⊕ n ]) accept) ->
  forall n, n < strind + 1 -> In (m Ⓑ[ strloc ⊕ n ]) accept.
Proof.
  intros.
  rewrite N.add_1_r in H1.
  rewrite N.lt_succ_r in H1.
  rewrite N.le_lteq in H1.
  destruct H1; subst; auto.
Qed.

Theorem substr_accept_mod m strloc strind accept :
  (forall n, n < strind -> In (m Ⓑ[ strloc ⊕ n ]) accept) ->
  forall n, n < strind mod 2^32 -> In (m Ⓑ[ strloc ⊕ n ]) accept.
Proof.
  intros.
  apply H.
  eapply N.lt_le_trans; [eassumption|].
  apply N_mod_le.
Qed.

Theorem substr_accept_xaddone m strloc strind accept :
  In (m Ⓑ[ strloc ⊕ strind ]) accept ->
  (forall n, n < strind -> In (m Ⓑ[ strloc ⊕ n ]) accept) ->
  forall n, n < strind ⊕ 1 -> In (m Ⓑ[ strloc ⊕ n ]) accept.
Proof.
  intros.
  eapply substr_accept_mod; [|apply H1].
  apply substr_accept_addone; auto.
Qed.

Theorem strspn_partial_correctness_loop:
  forall s strloc acceptloc accept sp m n s' x
         (MDL0: models armtypctx s)
         (MEM0: s V_MEM32 = Ⓜm) (SP0: s R_SP = Ⓓsp)
         (ARGSTRING: s R_R0 = Ⓓstrloc) (ARGACCEPT: s R_R1 = Ⓓacceptloc)
         (INITCHAR: s R_R12 = Ⓓm Ⓑ[strloc])
         (ACCEPT: cstring m acceptloc accept)
         (RET: strspn_arm s (m Ⓓ[ sp ⊕ 4 ]) = None)
         (XP0: exec_prog fh strspn_arm 16 s n s' x),
    trueif_inv (strspn_invset strloc acceptloc accept m strspn_arm x s').
Proof.
  intros.
  eapply prove_invs; [exact XP0|repeat split;assumption|].
  intros.
  assert (MDL: models armtypctx s1)
    by (eapply preservation_exec_prog; eauto; apply strspn_welltyped).
  assert (MEM: s1 V_MEM32 = Ⓜm) by admit.
  assert (SP: s1 R_SP = Ⓓsp) by admit.

  assert (WTM := arm_wtm MDL MEM).
  simpl in WTM.
  rewrite (strspn_nwc s1) in RET.
  apply (arm_regsize MDL0) in ARGSTRING.
  apply (arm_regsize MDL0) in ARGACCEPT.
  simpl in ARGSTRING,ARGACCEPT.

  destruct_inv 32 PRE.

  Local Ltac step := time arm_step.

  {
    repeat step.
    intuition.
    rewrite Hsv,Hsv0 in *.
    inversion H; subst.
    inversion H1; subst.
    rewrite H3.
    exists 0.
    rewrite N.add_0_r.
    rewrite N.mod_small by assumption.
    intuition.
  }
  {
    repeat step.
    {
      (* accept is empty *)
      unfold strspn_post.
      destruct PRE as [answer HPRE].
      intuition.
      rewrite Hsv in *.
      apply un_d_ify in H0.
      subst.
      exists answer.
      intuition; subst; intuition.
      apply Neqb_ok in BC.
      destruct (m Ⓑ[_]) eqn:R in BC; [|discriminate].
      destruct accept; [assumption|].
      red in H4.
      intuition.
    }
    {
      destruct PRE as [prestrind HPRE].
      intuition.
      rewrite Hsv in *.
      rewrite Hsv0 in *.
      rewrite Hsv1 in *.
      rewrite Hsv2 in *.
      Local Ltac un_d_ify :=
        repeat
          match goal with
          | [ HX : Ⓓ_ = Ⓓ_ |- _ ] => apply un_d_ify in HX
          end; subst.
      un_d_ify.
      eexists.
      split; [reflexivity|].
      psimpl_goal.
      rewrite N.add_assoc.
      intuition.
      assert (NG : In (m Ⓑ[ strloc ⊕ prestrind ]) accept); [|admit].
      apply Neqb_ok in BC0.
      destruct (_ =? 0) eqn:HEq in BC0; [|discriminate].
      apply Neqb_ok in HEq.
      unfold welltyped_memory in WTM.
      assert (WTM32 : forall a, m Ⓑ[ a ] < 2 ^ 32).
      {
        simpl.
        unfold getmem_little.
        intros.
        rewrite N.lor_0_r.
        eapply N.lt_trans; eauto.
        reflexivity.
      }
      apply mod_sub_eq in HEq; [|apply WTM32|apply WTM32].
      red in H4.
      destruct accept; [rewrite H4 in BC;discriminate|].
      left.
      rewrite HEq in H4.
      intuition.
      (* GOAL: all previous characters in accept -> next character in accept *)
    }
    {
      unfold strspn_post.
      rewrite Hsv in *.
      rewrite Hsv0 in *.
      rewrite Hsv1 in *.
      rewrite Hsv2 in *.
      destruct PRE as [prestrind HPRE].
      intuition.
      un_d_ify.
      rewrite N.eqb_neq in BC1.
      destruct (_ =? 0) eqn:HEq in BC1; [|contradiction].
      apply Neqb_ok in HEq.
      eexists.
      split; [reflexivity|].
      apply Neqb_ok in BC0.
      destruct (_ =? _) eqn:HEq1 in BC0; [|discriminate].
      apply Neqb_ok in HEq1.
      assert (WTM32 : forall a, m Ⓑ[ a ] < 2 ^ 32).
      {
        simpl.
        unfold getmem_little.
        intros.
        rewrite N.lor_0_r.
        eapply N.lt_trans; eauto.
        reflexivity.
      }
      apply mod_sub_eq in HEq1; [|apply WTM32|apply WTM32].
      assert (cstr_nonil: forall m loc s, cstring m loc s -> ~In 0 s).
      {
        intros.
        generalize dependent loc.
        induction s0; [tauto|].
        intros.
        simpl in H.
        simpl.
        intuition.
        eapply IHs0; eassumption.
      }
      split; [assumption|].
      split.
      {
        admit.
      }
      {
        rewrite N.add_mod_idemp_r by discriminate.
        rewrite N.add_assoc.
        rewrite N.add_mod_idemp_l in HEq by discriminate.
        replace (m Ⓑ[ strloc + prestrind ⊕ 1 ]) with 0.
        2: {
          rewrite <- HEq.
          simpl.
          unfold getmem_little.
          rewrite N.lor_0_r.
          reflexivity.
        }
        eapply cstr_nonil.
        eassumption.
      }
    }
    {
      rewrite Hsv in *.
      rewrite Hsv0 in *.
      rewrite Hsv1 in *.
      destruct PRE as [strind HPRE].
      intuition.
      un_d_ify.
      exists strind,0.
      rewrite N.add_0_r.
      rewrite N.mod_small by assumption.
      intuition.
      simpl.
      unfold getmem_little.
      rewrite N.lor_0_r.
      reflexivity.
    }
  }
  {
    repeat step.
    {
      admit.
    }
    {
      admit.
    }
    {
      admit.
    }
    {
      admit.
    }
  }
Abort.
