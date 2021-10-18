Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv7.
Require Import strlen_arm.

Import ARM7Notations.
Open Scope N.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

Theorem strlen_nwc: forall s2 s1, strlen_arm s1 = strlen_arm s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog arm7typctx strlen_arm.
Proof.
  Picinae_typecheck.
Qed.

Theorem strlen_preserves_memory:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

Theorem strlen_preserves_readable:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

Theorem strlen_preserves_lr:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' R_LR = s R_LR.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Definition nilfree (m:addr->N) (p:addr) (k:N) :=
  forall i, i < k -> m (p⊕i) <> 0.

Definition strlen_invs (m:addr->N) (p a:addr) (s:store) :=
  match a with
  | 0 => Some (s R_R0 = Ⓓp)
  | 40 => Some (∃ k, s R_R0 = Ⓓ(2^32 - p mod 4 ⊕ 4*k) /\
                     s R_R1 = Ⓓ(p - p mod 4 ⊕ 4*N.succ k) /\
                     s R_R2 = Ⓓ match k with N0 => m Ⓓ[ p - p mod 4 ] .| N.ones (p mod 4 * 8)
                                           | _ => m Ⓓ[ p - p mod 4 ⊕ 4*k ] end /\
                     nilfree m p (4*k - p mod 4))
  | _ => None
  end.

Definition strlen_post (m:addr->N) (p:addr) (_:exit) (s:store) :=
  ∃ k, s R_R0 = Ⓓk /\ nilfree m p k /\ m (p⊕k) = 0.

Definition strlen_invset (m:addr->N) (p:addr) :=
  invs (strlen_invs m p) (strlen_post m p).

Lemma modsubcmp:
  forall x y z, y <= x -> (x - y =? z) = (x =? z+y).
Proof.
  intros. destruct (x =? z + y) eqn:H1.
    apply Neqb_ok in H1. subst. rewrite N.add_sub. apply N.eqb_refl.
    apply N.eqb_neq. intro H2. eapply N.eqb_neq. exact H1. subst. rewrite N.sub_add by exact H. reflexivity.
Qed.

Lemma ldiff_sub:
  forall x y, N.ldiff x y = x - (x .& y).
Proof.
  intros. rewrite N.sub_nocarry_ldiff; apply N.bits_inj; intro n;
  rewrite 2?N.ldiff_spec, N.land_spec, 1?N.bits_0;
  repeat destruct (N.testbit _ _); reflexivity.
Qed.

Lemma nilfree_mod:
  forall m p a x, nilfree m p a -> nilfree m p (a mod 2^x).
Proof.
  intros. intros i LT. apply H. eapply N.lt_le_trans. exact LT.
  apply N.mod_le. apply N.pow_nonzero. discriminate.
Qed.

Lemma index_bound:
  forall p k j, p < 2^32 -> j < 4 -> p - p mod 4 ⊕ 4*k + j < 2^32.
Proof.
  intros. change (2^32) with (4*2^30) at 1. change (2^32) with (4*N.pred (2^30) + 4).
  rewrite (N.div_mod' p 4) at 1.
  rewrite N.add_sub, <- N.mul_add_distr_l, N.mul_mod_distr_l by discriminate.
    apply N.add_le_lt_mono; [|assumption].
    apply N.mul_le_mono_l, N.lt_le_pred, N.mod_lt. discriminate.
Qed.

Lemma getbyte_lor:
  forall i x len m a (WTM: welltyped_memory m),
  i<len -> (getmem LittleE len m a .| x) .& (N.ones 8 << (8*i)) = (m (a+i) .| ((x >> (8*i)) mod 2^8)) << (8*i).
Proof.
  intros.
  rewrite <- (N.sub_add i len), N.add_comm, getmem_split by apply N.lt_le_incl, H.
  rewrite <- (recompose_bytes (8*i) x) at 1.
  rewrite N.lor_assoc, <- (N.lor_assoc (getmem _ i m a)), (N.lor_comm _ (_ mod _)), N.lor_assoc, <- N.lor_assoc,
          N.land_lor_distr_l, (N.bits_inj_0 (_ .& _)).
  rewrite N.lor_0_l, <- N.shiftl_lor, <- N.shiftl_land, <- (N.succ_pred (len-i)) by apply N.sub_gt, H.
  rewrite getmem_succ, 2!N.land_lor_distr_l, 3!N.land_ones, (N.shiftl_mul_pow2 _ Mb).
  rewrite N.mod_mul, N.lor_0_r by (apply N.pow_nonzero; discriminate).
  rewrite N.mod_small by apply WTM. reflexivity.

  intro n. rewrite <- N.land_ones, N.land_spec, N.lor_spec, N.land_spec. destruct (N.le_gt_cases (8*i) n).
    erewrite N.ones_spec_high, (bound_hibits_zero _ (getmem _ _ _ _)), Bool.andb_false_r;
    [ reflexivity | apply getmem_bound | |]; assumption.
    rewrite N.shiftl_spec_low by assumption. apply Bool.andb_false_r.
Qed.

Corollary getbyte:
  forall i len m a (WTM: welltyped_memory m),
  i<len -> getmem LittleE len m a .& (N.ones 8 << (8*i)) = m (a+i) << (8*i).
Proof.
  intros. rewrite <- (N.lor_0_r (getmem _ _ _ _)).
  rewrite getbyte_lor by assumption. rewrite N.shiftr_0_l, N.lor_0_r.
  reflexivity.
Qed.

Lemma simpl_bc:
  forall (b:bool) p, (if b then 0 else 1) = N.pos p -> (if b then 0 else 1) = 1.
Proof.
  intros. destruct b. discriminate. reflexivity.
Qed.

Lemma nilfree_extend:
  forall j m p k (WTM: welltyped_memory m) (P32: p < 2^32) (J4: j <= 4)
         (NF: nilfree m p (4*k - p mod 4))
         (NN: forall i, i < j ->
              (if (if k then getmem LittleE (N.succ i) m (p - p mod 4) .| N.ones (p mod 4 * 8)
                        else getmem LittleE (N.succ i) m (p - p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*i)) =? 0
               then 0 else 1) = 1),
  nilfree m p (4*k + j - p mod 4).
Proof.
  intros. intros i LT. destruct k as [|k].

    rewrite N.add_0_l in LT. rewrite N.mod_small.

      apply N.lt_add_lt_sub_l in LT.
      specialize (NN _ LT). rewrite getbyte_lor in NN by solve [ assumption | apply N.lt_succ_diag_r ].
      rewrite N.add_assoc, N.sub_add in NN by (apply N.mod_le; discriminate).
      intro H. rewrite H in NN. rewrite N.lor_0_l in NN.
      rewrite shiftr_low_pow2 in NN.
        rewrite N.mod_0_l, N.shiftl_0_l in NN; [|apply N.pow_nonzero]; discriminate.
        rewrite N.mul_comm. eapply N.lt_le_trans.
          apply ones_bound.
          apply N.pow_le_mono_r. discriminate. apply N.mul_le_mono_l, N.le_add_r.

      rewrite (N.div_mod' p 4). eapply N.lt_le_trans.
        apply N.add_lt_mono_l. exact LT.
        rewrite N.add_sub_assoc, N.add_comm, N.add_assoc, N.add_sub, N.add_comm.
          change (2^32) with (4*N.pred (2^30) + 4). apply N.add_le_mono; [|assumption].
            apply N.mul_le_mono_l, N.lt_le_pred, N.div_lt_upper_bound, P32. discriminate.
          intro H. apply N.gt_lt, N.lt_le_incl, N.sub_0_le in H. rewrite H in LT. destruct i; discriminate.

    destruct (N.lt_ge_cases i (4*N.pos k - p mod 4)). apply NF, H.
    intro H1. assert (H2: p mod 4 <= 4 * N.pos k). transitivity (4*1).
      apply N.lt_le_incl, N.mod_lt. discriminate.
      apply N.mul_le_mono_l. destruct k; discriminate.
    rewrite N.add_sub_swap, N.add_comm, <- (N.sub_add _ _ H) in LT by exact H2.
    apply N.add_lt_mono_r in LT. specialize (NN _ LT).
    rewrite getbyte in NN by solve [ assumption | apply N.lt_succ_diag_r ].
    rewrite <- (N.mod_small (_+_) (2^32)) in NN by (apply index_bound; [|eapply N.lt_le_trans]; eassumption).
    rewrite N.add_mod_idemp_l in NN by (apply N.pow_nonzero; discriminate).
    rewrite <- N.add_sub_swap in NN by (apply N.mod_le; discriminate).
    rewrite <- N.add_sub_assoc, (N.add_sub_assoc _ i) in NN by assumption.
    rewrite <- (N.add_assoc p), (N.add_comm _ i), (N.add_assoc p), N.add_sub, H1, N.shiftl_0_l in NN.
    discriminate.
Qed.

Theorem nilterminate:
  forall j m p k (WTM: welltyped_memory m) (P32: p < 2^32) (J4: j < 4)
         (NF: nilfree m p (4*k - p mod 4))
         (NN: forall i, i < j ->
              (if (if k then getmem LittleE (N.succ i) m (p - p mod 4) .| N.ones (p mod 4 * 8)
                        else getmem LittleE (N.succ i) m (p - p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*i)) =? 0
               then 0 else 1) = 1)
         (NIL: (if (if k then getmem LittleE (N.succ j) m (p - p mod 4) .| N.ones (p mod 4 * 8)
                         else getmem LittleE (N.succ j) m (p - p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*j)) =? 0
                 then 0 else 1) = 0),
  nilfree m p (2^32 - p mod 4 + 4*k ⊕ j) /\
  m (p ⊕ (2^32 - p mod 4 + 4*k ⊕ j)) = 0.
Proof.
  intros.
  destruct N.land eqn:H in NIL; [|discriminate]. clear NIL. rename H into NIL.
  rewrite <- !N.add_assoc. split.

  rewrite <- N.add_sub_swap by (transitivity 4; try apply N.lt_le_incl, N.mod_lt; discriminate).
  rewrite <- N.add_sub_assoc.
  rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate.
  apply nilfree_mod.
  apply nilfree_extend; try apply N.lt_le_incl; assumption.
  destruct k as [|k].

    rewrite N.add_0_l. intro H. apply N.gt_lt in H.
    rewrite getbyte_lor, N.mul_comm in NIL by first [ assumption | apply N.lt_succ_diag_r ].
    rewrite N.shiftr_div_pow2, N.ones_div_pow2 in NIL by apply N.mul_le_mono_l, N.lt_le_incl, H.
    rewrite <- N.mul_sub_distr_l, N.lor_comm in NIL.
    rewrite N.ones_mod_pow2 in NIL by (change 8 with (8*N.succ 0) at 1;
      apply N.mul_le_mono_l, N.le_succ_l, N.neq_0_lt_0, N.sub_gt, H).
    apply N.shiftl_eq_0_iff, N.lor_eq_0_l in NIL. discriminate.

    transitivity 4.
      apply N.lt_le_incl, N.mod_lt. discriminate.
      etransitivity. apply N.le_add_r. apply N.add_le_mono_r. destruct k; discriminate.

  rewrite N.add_mod_idemp_r, N.add_assoc by discriminate.
  rewrite N.add_sub_assoc by (transitivity 4; [apply N.lt_le_incl, N.mod_lt|]; discriminate).
  rewrite (N.add_comm p), <- N.add_sub_assoc by (apply N.mod_le; discriminate).
  rewrite <- N.add_assoc, <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate.
  rewrite N.add_assoc. rewrite <- N.add_mod_idemp_l by discriminate.
  rewrite N.mod_small by (apply index_bound; assumption).
  destruct k as [|k].

    rewrite getbyte_lor in NIL by first [ assumption | apply N.lt_succ_diag_r ].
    apply N.shiftl_eq_0_iff, N.lor_eq_0_l in NIL.
    rewrite N.mul_0_r, N.add_0_r, N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply P32 ]).
    exact NIL.

    rewrite getbyte in NIL by first [ assumption | apply N.lt_succ_diag_r ].
    apply N.shiftl_eq_0_iff in NIL. exact NIL.
Qed.

Theorem strlen_partial_correctness:
  forall s p lr m n s' x
         (MDL0: models arm7typctx s)
         (MEM0: s V_MEM32 = Ⓜm) (LR0: s R_LR = Ⓓlr) (R0: s R_R0 = Ⓓp)
         (RET: strlen_arm s lr = None)
         (XP0: exec_prog fh strlen_arm 0 s n s' x),
  trueif_inv (strlen_invset m p strlen_arm x s').
Proof.
  intros.
  eapply prove_invs. exact XP0.
  exact R0.
  intros.
  assert (MDL: models arm7typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strlen_welltyped. exact XP.
  assert (MEM: s1 V_MEM32 = Ⓜm).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  assert (LR: s1 R_LR = Ⓓlr).
    rewrite <- LR0. eapply strlen_preserves_lr. eassumption.
  assert (WTM := arm7_wtm MDL MEM). simpl in WTM.
  rewrite (strlen_nwc s1) in RET.
  apply (arm7_regsize MDL0) in R0. simpl in R0. rename R0 into P32.
  clear s MDL0 MEM0 LR0 XP XP0.

  destruct_inv 32 PRE.

  Local Ltac step := time arm7_step.

  (* Address 0 *)
  step. step. step. step.
    rewrite <- N.ldiff_land_low by (destruct p; [|apply N.log2_lt_pow2;[|apply (arm7_regsize MDL PRE)]]; reflexivity).
    change 3 with (N.ones 2). rewrite ldiff_sub, N.land_ones.
  step. exists 0.
    apply Neqb_ok in BC. destruct (p mod 4); [|discriminate BC]. rewrite !N.sub_0_r, N.mul_0_r, N.lor_0_r. repeat split.
    intros i LT. destruct i; discriminate.
  step. step.
    apply N.eqb_neq in BC.
    assert (LE1: 1 <= p mod 4). destruct (p mod _). contradict BC. reflexivity. destruct p0; discriminate.
    rewrite <- N.add_sub_assoc by exact LE1.
    rewrite <- (N.add_mod_idemp_l (2^32)), N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate).
    assert (H: p mod 4 - 1 < 2^31). eapply N.le_lt_trans, N.lt_le_trans. apply N.le_sub_l. apply N.mod_lt. discriminate. discriminate.
    rewrite (N.mod_small (_-1)) by (etransitivity; [exact H | reflexivity]).
    rewrite shiftr_low_pow2 by exact H. clear H.
    rewrite modsubcmp by exact LE1.
  step. step.
    destruct (p mod 4 =? 1) eqn:BC1; [clear BC0|discriminate].
    apply Neqb_ok in BC1. rewrite BC1, N.sub_diag, N.add_0_r.
  step. exists 0.
    change (2^2) with 4 in BC1. rewrite BC1. repeat split.
    intros i LT. destruct i; discriminate.
  step.
    destruct (p mod 4 =? 1) eqn:BC1; [discriminate|clear BC0]. apply N.eqb_neq in BC1.
    assert (LE2: 1 <= p mod 4 - 1). destruct (p mod 4). contradict BC;reflexivity. repeat (discriminate + (contradict BC1;reflexivity) + destruct p1).
    rewrite <- N.add_sub_assoc by exact LE2.
    rewrite <- (N.add_mod_idemp_l (2^32)), N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate).
    assert (H: p mod 4 - 1 - 1 < 2^31). eapply N.le_lt_trans, N.le_lt_trans, N.lt_le_trans; try (apply N.mod_lt + apply N.le_sub_l); discriminate.
    rewrite (N.mod_small (_-1)) by (etransitivity; [exact H | reflexivity]).
    rewrite shiftr_low_pow2 by exact H. clear H.
    rewrite 2!modsubcmp by (exact LE1 + exact LE2).
  step.
    exists 0. destruct (p mod 4 =? 2) eqn:BC2; [clear BC0|discriminate].
      apply Neqb_ok in BC2. rewrite BC2, <- N.lor_assoc. repeat split.
      intros i LT. destruct i; discriminate.
    exists 0. replace (p mod 4) with 3.
      rewrite <- !N.lor_assoc. repeat split. intros i LT. destruct i; discriminate.
      assert (LT3: p mod 4 < 4). apply N.mod_lt. discriminate.
      destruct (p mod 4). contradict BC; reflexivity. repeat (discriminate + destruct p2). reflexivity. exfalso. apply LE2. reflexivity.

  (* Address 40 *)
  destruct PRE as [k [R0 [R1 [R2 NF]]]].
  repeat (discriminate + step).
  all: match goal with [ m: addr -> N |- _ ] => match goal with [ H: context [ m _ ] |- _ ] =>
    rewrite <- !(getmem_1 LittleE m), <- N.land_ones in H;
    change (N.ones 8) with (N.ones 8 << (8*0)) in H
  end end.

    (* nil at offset 4k+0 *)
    eexists. psimpl. split. reflexivity. rewrite <- (N.add_0_r (_+_)). apply nilterminate; try assumption. reflexivity.
    intros i LT. destruct i; discriminate LT.

    (* nil at offset 4k+1 *)
    eexists. psimpl. split. reflexivity. apply nilterminate; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT + (eapply simpl_bc; eassumption) + destruct i as [i|i|]).

    (* nil at offset 4k+2 *)
    eexists. psimpl. split. reflexivity. apply nilterminate; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT + (eapply simpl_bc; eassumption) + destruct i as [i|i|]).

    (* nil at offset 4k+3 *)
    eexists. psimpl. split. reflexivity. apply nilterminate; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT + (eapply simpl_bc; eassumption) + destruct i as [i|i|]).

    (* no nils from 4k+0 to 4k+3: iterate loop *)
    exists (N.succ k). rewrite <- !N.add_assoc, <- !N.mul_succ_r. repeat split.
      destruct k; reflexivity.
      rewrite N.mul_succ_r. apply nilfree_extend; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT + (eapply simpl_bc; eassumption) + destruct i as [i|i|]).
Qed.
