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

Definition cstringlen m loc len :=
  (forall i, i < len -> m (loc ⊕ len) <> 0) /\ m (loc ⊕ len) = 0.

Theorem cstringlen_det m loc len1 len2 :
  cstringlen m loc len1 -> cstringlen m loc len2 -> len1 = len2.
Proof.
  unfold cstringlen.
  intuition.
  specialize (H1 len2).
  specialize (H len1).
  destruct (N.compare_spec len1 len2); tauto.
Qed.

Definition cstringmem m loc c :=
  exists cind, (forall i, i <= cind -> m (loc ⊕ i) <> 0) /\ c = m (loc ⊕ cind).

Theorem cstr_mematind m loc len cind :
  cstringlen m loc len -> cind < len -> cstringmem m loc (m (loc ⊕ cind)).
Proof.
  unfold cstringlen,cstringmem.
  intros.
  exists cind.
  intuition.
  eauto.
Qed.

Theorem cstr_nonil m loc : ~cstringmem m loc 0.
Proof.
  unfold cstringmem,cstringlen.
  intro H.
  destruct H as [? [H1 H2]].
  rewrite H2 in H1.
  eapply H1; [|reflexivity].
  apply N.le_refl.
Qed.

Definition strspn_post m str accept (_ : exit) s :=
  exists answer,
    s R_R0 = Ⓓanswer /\
    (forall n, n < answer -> cstringmem m accept (m (str ⊕ n))) /\
    ~cstringmem m accept (m (str ⊕ answer)).

Definition strspn_invs m sp str accept a s :=
  match a with
  | 16 =>
    Some (s R_R0 = Ⓓstr /\
          s R_R1 = Ⓓaccept /\
          s V_MEM32 = Ⓜm /\
          s R_SP = Ⓓsp /\
          s R_R12 = Ⓓ(m str))
  | 28 =>
    Some
      (exists strind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓaccept /\
          s R_R4 = Ⓓ(m accept) /\
          s R_R12 = Ⓓ(m (str⊕strind)) /\
          s R_LR = Ⓓ(str⊕strind) /\
          s V_MEM32 = Ⓜm /\
          s R_SP = Ⓓsp /\
          forall i, i < strind -> cstringmem m accept (m (str⊕i)))
  | 60 =>
    Some
      (exists strind acceptind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓaccept /\
          s R_R2 = Ⓓ(accept⊕acceptind) /\
          s R_R4 = Ⓓ(m accept) /\
          s R_R12 = Ⓓ(m (str⊕strind)) /\
          s R_LR = Ⓓ(str⊕strind) /\
          s V_MEM32 = Ⓜm /\
          s R_SP = Ⓓsp /\
          (forall i, i < strind -> cstringmem m accept (m (str⊕i))) /\
          (forall i, i <= acceptind ->
                     m (accept⊕i) <> 0 /\
                     m (str⊕strind) <> m (accept⊕i)))
  | _ => None
  end.

Definition strspn_invset m sp str accept :=
  invs (strspn_invs m sp str accept)
       (strspn_post m str accept).

Theorem sub_self_sub n m : n < m -> m - (m - n) = n.
Proof.
  intros.
  apply N.add_sub_eq_r.
  rewrite N.add_sub_assoc by (apply N.lt_le_incl; assumption).
  rewrite N.add_sub_swap by apply N.le_refl.
  rewrite N.sub_diag.
  apply N.add_0_l.
Qed.

Theorem add_sub_sub x n m :
  n < m -> m < x -> x + n - m = x - (m - n).
Proof.
  intros.
  apply (Nplus_reg_l m).
  repeat rewrite (N.add_comm m).
  rewrite (N.sub_add m) by apply N.lt_le_incl,N.lt_lt_add_r,H0.
  rewrite <- N.add_sub_swap by
      eauto using N.le_trans,N.lt_le_incl,N.le_sub_l.
  rewrite <- N.add_sub_assoc by apply N.le_sub_l.
  f_equal.
  clear x H0.
  symmetry.
  apply sub_self_sub.
  assumption.
Qed.

Theorem mod_sub_eq n m x :
  n < x -> m < x -> ((x + n) - m) mod x = 0 -> n = m.
Proof.
  intros.
  destruct (N.compare_spec n m); [assumption| |].
  {
    rewrite N.mod_small in H1.
    {
      exfalso.
      rewrite N.sub_0_le in H1.
      apply (N.lt_irrefl x).
      eapply N.le_lt_trans; [|eassumption].
      eapply N.le_trans; [|eassumption].
      apply N.le_add_r.
    }
    {
      rewrite add_sub_sub; auto.
      apply N.sub_lt; [|apply N.lt_add_lt_sub_l; rewrite N.add_0_r; assumption].
      eapply N.lt_le_incl, N.le_lt_trans; [apply N.le_sub_l|eassumption].
    }
  }
  {
    exfalso.
    rewrite <- N.add_sub_assoc in H1; eauto using N.lt_le_incl.
    assert (x <> 0) by (intro; subst; eapply N.nlt_0_r; eassumption).
    rewrite <- N.add_mod_idemp_l,N.mod_same,N.add_0_l in H1 by eassumption.
    rewrite N.mod_small in H1 by
        eauto using N.le_lt_trans,N.le_sub_l.
    rewrite N.sub_0_le in H1.
    rewrite N.le_ngt in H1.
    tauto.
  }
Qed.

Theorem cstr_straccept_next' m str accept strind :
  (forall i, i < strind -> cstringmem m accept (m (str ⊕ i))) ->
  cstringmem m accept (m (str ⊕ strind)) ->
  (forall i, i < strind + 1 -> cstringmem m accept (m (str ⊕ i))).
Proof.
  unfold cstringmem.
  intros.
  destruct (N.ltb_spec i strind); [apply H; assumption|].
  destruct H0 as [cind ?].
  exists cind.
  assert (i = strind); subst; [|assumption].
  apply N.le_antisymm; [|assumption].
  apply N.lt_succ_r.
  rewrite <- N.add_1_r.
  assumption.
Qed.

Theorem cstr_straccept_mod m str accept strind :
  (forall i, i < strind -> cstringmem m accept (m (str ⊕ i))) ->
  (forall i, i < strind mod (2^32) -> cstringmem m accept (m (str ⊕ i))).
Proof.
  intros.
  apply H.
  eapply N.lt_le_trans; [eassumption|].
  apply N.mod_le.
  discriminate.
Qed.

Theorem cstr_straccept_next m str accept strind :
  (forall i, i < strind -> cstringmem m accept (m (str ⊕ i))) ->
  cstringmem m accept (m (str ⊕ strind)) ->
  (forall i, i < strind ⊕ 1 -> cstringmem m accept (m (str ⊕ i))).
Proof.
  intros H1 H2.
  eapply cstr_straccept_mod.
  eapply cstr_straccept_next'; assumption.
Qed.

Theorem cstring_nonnil_next' m loc ind :
  (forall i, i < ind -> m (loc ⊕ i) <> 0) ->
  m (loc ⊕ ind) <> 0 ->
  (forall i, i < (ind+1) -> m (loc ⊕ i) <> 0).
Proof.
  intros.
  specialize (H i).
  rewrite N.add_1_r in H1.
  rewrite N.lt_succ_r in H1.
  rewrite N.lt_eq_cases in H1.
  intuition.
  subst.
  tauto.
Qed.
Theorem cstring_nonnil_mod m loc ind x :
  (forall i, i < ind -> m (loc ⊕ i) <> 0) ->
  (forall i, i < (ind mod x) -> m (loc ⊕ i) <> 0).
Proof.
  intros.
  apply H.
  eapply N.lt_le_trans; [eassumption|].
  apply N_mod_le.
Qed.
Theorem cstring_nonnil_next m loc ind :
  (forall i, i < ind -> m (loc ⊕ i) <> 0) ->
  m (loc ⊕ ind) <> 0 ->
  (forall i, i < (ind ⊕ 1) -> m (loc ⊕ i) <> 0).
Proof.
  intros ? ?.
  apply cstring_nonnil_mod,cstring_nonnil_next'; assumption.
Qed.
Theorem cstring_nonnil_le' m loc ind :
  (forall i, i <= ind -> m (loc ⊕ i) <> 0) <->
  (forall i, i < (ind + 1) -> m (loc ⊕ i) <> 0).
Proof.
  assert (HX := fun n => N.lt_succ_r n ind).
  intuition; specialize (HX i); specialize (H i); intuition.
Qed.
Theorem cstring_nonnil_le m loc ind :
  (forall i, i <= ind -> m (loc ⊕ i) <> 0) ->
  (forall i, i < (ind ⊕ 1) -> m (loc ⊕ i) <> 0).
Proof.
  intro.
  apply cstring_nonnil_mod, cstring_nonnil_le'.
  assumption.
Qed.
Theorem cstring_nonnil_le_next m loc ind :
  (forall i, i <= ind -> m (loc ⊕ i) <> 0) ->
  m (loc + ind ⊕ 1) <> 0 ->
  (forall i, i <= (ind ⊕ 1) -> m (loc ⊕ i) <> 0).
Proof.
  intros.
  rewrite N.lt_eq_cases in H1.
  destruct H1; [|subst; psimpl (_⊕_); rewrite N.add_assoc; assumption].
  eapply cstring_nonnil_le; eassumption.
Qed.

Local Ltac eq_unbool :=
  repeat
    match goal with
    | [ H : context[if ?x =? ?y then _ else _] |- _ ] =>
      destruct (N.eqb_spec x y); try discriminate
    end.

Theorem strspn_partial_correctness_loop:
  forall s str accept sp m n s' x
         (MDL0: models armtypctx s)
         (MEM0: s V_MEM32 = Ⓜm) (SP0: s R_SP = Ⓓsp)
         (ARGSTRING: s R_R0 = Ⓓstr) (ARGACCEPT: s R_R1 = Ⓓaccept)
         (INITCHAR: s R_R12 = Ⓓm str)
         (RET: strspn_arm s (m Ⓓ[ sp ⊕ 4 ]) = None)
         (XP0: exec_prog fh strspn_arm 16 s n s' x),
    trueif_inv (strspn_invset m sp str accept strspn_arm x s').
Proof.
  intros.
  eapply prove_invs; [exact XP0|repeat split;assumption|].
  intros.
  assert (MDL: models armtypctx s1)
    by (eapply preservation_exec_prog; eauto; apply strspn_welltyped).
  assert (WTM := arm_wtm MDL0 MEM0).
  simpl in WTM.
  assert (WTM32 : forall a, m a < 2 ^ 32).
  {
    intros.
    eapply N.lt_trans; eauto.
    reflexivity.
  }
  rewrite (strspn_nwc s1) in RET.
  apply (arm_regsize MDL0) in ARGSTRING.
  apply (arm_regsize MDL0) in ARGACCEPT.
  simpl in ARGSTRING,ARGACCEPT.

  destruct_inv 32 PRE.

  Local Ltac step := time arm_step.

  {
    intuition.
    repeat step.
    exists 0.
    psimpl_goal.
    intuition.
  }
  {
    destruct PRE as [prestrind HPRE].
    intuition.
    repeat step.
    {
      (* accept is empty *)
      unfold strspn_post.
      psimpl_goal.
      destruct (N.eqb_spec (m accept) 0); [|discriminate].
      exists prestrind.
      intuition.
      destruct H6.
      intuition.
      eapply (H8 0); [apply N.le_0_l|].
      psimpl (_ mod _).
      assumption.
    }
    {
      eexists.
      split; [reflexivity|].
      psimpl_goal.
      rewrite N.add_assoc.
      intuition.
      eapply cstr_straccept_next; eauto.
      unfold cstringmem.
      destruct (_ =? _) eqn:HEq in BC0 at 2; [|discriminate].
      apply Neqb_ok in HEq.
      apply mod_sub_eq in HEq; auto.
      destruct (N.eqb_spec (m accept) 0); [discriminate|].
      exists 0.
      psimpl (_ ⊕ 0).
      intuition.
      apply N.le_0_r in H8.
      subst.
      psimpl (_ ⊕ 0) in H9.
      tauto.
      (* GOAL: all previous characters in accept -> next character in accept *)
    }
    {
      unfold strspn_post.
      psimpl_goal.
      eexists.
      split; [reflexivity|].
      psimpl_goal.
      psimpl (str ⊕ _).
      eq_unbool.
      apply mod_sub_eq in e0; auto.
      rewrite N.add_assoc,e.
      split; [|apply cstr_nonil].
      apply cstr_straccept_next; [assumption|].
      exists 0.
      psimpl (_ ⊕ 0).
      intuition.
      apply N.le_0_r in H6.
      subst.
      psimpl (_ ⊕ 0) in H8.
      tauto.
    }
    {
      exists prestrind,0.
      eq_unbool.
      psimpl (_ ⊕ 0).
      Search (_ <= 0).
      assert (HA: accept ⊕ 0 = accept) by (psimpl (_ ⊕ 0); reflexivity).
      intuition; rewrite N.le_0_r in *; subst; rewrite HA in *; auto.
      apply n0.
      rewrite H8.
      psimpl (_ mod _).
      reflexivity.
    }
  }
  {
    destruct PRE as [pstrind [pacceptind HPRE]].
    intuition.
    repeat step.
    {
      eq_unbool.
      apply mod_sub_eq in e; auto.
      eexists.
      split; [reflexivity|].
      psimpl_goal.
      rewrite N.add_assoc.
      intuition.
      eapply cstr_straccept_next; eauto.
      exists (pacceptind+1).
      rewrite N.add_assoc.
      intuition.
      rewrite N.add_1_r in H10.
      rewrite N.le_succ_r in H10.
      destruct H10; [destruct (H9 i0); [assumption|tauto]|].
      subst.
      apply n2.
      rewrite <- N.add_1_r,N.add_assoc in H11.
      assumption.
    }
    {
      eq_unbool.
      unfold strspn_post.
      psimpl_goal.
      eexists.
      split; [reflexivity|].
      psimpl (_ ⊕ (_ ⊕ _)).
      rewrite N.add_assoc,e.
      split; [|apply cstr_nonil].
      apply cstr_straccept_next; [assumption|].
      apply mod_sub_eq in e0; auto.
      unfold cstringmem.
      rewrite <- e0.
      exists (pacceptind + 1).
      rewrite N.add_assoc.
      split; [|reflexivity].
      intros.
      rewrite N.add_1_r in H8.
      rewrite N.le_succ_r in H8.
      destruct H8; [destruct (H9 i); [assumption|tauto]|].
      subst.
      rewrite <- N.add_1_r,N.add_assoc.
      assumption.
    }
    {
      eq_unbool.
      exists pstrind, (pacceptind⊕1).
      psimpl_goal.
      rewrite N.add_assoc.
      intuition.
      {
        eapply cstring_nonnil_le_next; eauto.
        intros.
        specialize (H9 i0).
        intuition.
      }
      {
        apply (N.le_trans i _ (pacceptind+1)) in H8; [|apply N_mod_le].
        rewrite N.lt_eq_cases in H8.
        rewrite N.add_1_r in H8 at 1.
        rewrite N.lt_succ_r in H8.
        specialize (H9 i).
        rewrite H10 in n0.
        intuition.
        subst.
        apply n0.
        rewrite N.add_assoc.
        psimpl (_ mod _).
        reflexivity.
      }
    }
    {
      eq_unbool.
      unfold strspn_post.
      psimpl_goal.
      eexists.
      split; [eassumption|].
      split; [assumption|].
      intro.
      destruct H8 as [i [HX1 HX2]].
      destruct (N.compare_spec i (pacceptind ⊕ 1)).
      {
        subst.
        eapply HX1; [apply N.le_refl|].
        psimpl (_ mod _).
        rewrite N.add_assoc.
        assumption.
      }
      {
        eapply N.lt_le_trans in H8; [|apply N_mod_le].
        rewrite N.add_1_r,N.lt_succ_r in H8.
        apply H9 in H8.
        tauto.
      }
      {
        apply (HX1 (pacceptind ⊕ 1)); [apply N.lt_le_incl; assumption|].
        (* REDUNDANT? *)
        psimpl (_ mod _).
        rewrite N.add_assoc.
        assumption.
      }
    }
  }
Qed.
