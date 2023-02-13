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

(* The ARM7 lifter creates non-writable code sections. *)
Theorem strlen_nwc: forall s2 s1, strlen_arm s1 = strlen_arm s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem strlen_welltyped: welltyped_prog arm7typctx strlen_arm.
Proof.
  Picinae_typecheck.
Qed.

(* Strlen does not corrupt memory. *)
Theorem strlen_preserves_memory:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

(* Strlen does not modify page permissions. *)
Theorem strlen_preserves_readable:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

(* Strlen does not corrupt the LR register (call-return safety). *)
Theorem strlen_preserves_lr:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' R_LR = s R_LR.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

(* Correctness specification for strlen: *)
Definition nilfree (m:addr->N) (p:addr) (k:N) :=
  forall i, i < k -> m Ⓑ[p+i] <> 0.

Definition strlen_post (m:addr->N) (p:addr) (_:exit) (s:store) :=
  ∃ k, s R_R0 = Ⓓk /\ nilfree m p k /\ m Ⓑ[p+k] = 0.

(* Loop invariants for verifying the specification (not trusted). *)
Definition strlen_invs (m:addr->N) (p a:addr) (s:store) :=
  match a with
  | 0 => Some (s R_R0 = Ⓓp)
  | 40 => Some (∃ k, s R_R0 = Ⓓ(4*k ⊖ p mod 4) /\
                     s R_R1 = Ⓓ(p ⊖ p mod 4 ⊕ 4*N.succ k) /\
                     s R_R2 = Ⓓ match k with N0 => m Ⓓ[ p ⊖ p mod 4 ] .| N.ones (p mod 4 * 8)
                                           | _ => m Ⓓ[ p ⊖ p mod 4 ⊕ 4*k ] end /\
                     nilfree m p (4*k - p mod 4))
  | _ => None
  end.

Definition strlen_invset (m:addr->N) (p:addr) :=
  invs (strlen_invs m p) (strlen_post m p).


(* Before proving correctness, prove some helper lemmas about binary arithmetic
   operations associated with our specification: *)

Lemma nilfree_mod:
  forall m p a w, nilfree m p a -> nilfree m p (a mod 2^w).
Proof.
  intros. intros i LT. apply H. eapply N.lt_le_trans. exact LT.
  apply N.mod_le. apply N.pow_nonzero. discriminate.
Qed.

Lemma getbyte:
  forall len m a,
  getmem 32 LittleE (N.succ len) m a .& (N.ones 8 << (8*len)) = m Ⓑ[a+len] << (8*len).
Proof.
  intros. rewrite <- N.add_1_r, getmem_split, N.land_lor_distr_l, <- N.shiftl_land.
  rewrite N.land_ones, N.mod_small by apply getmem_bound. replace (_.&_) with 0. reflexivity.
  symmetry. apply N.bits_inj_0. intro b.
  rewrite N.land_spec. destruct (N.lt_ge_cases b (8*len)).
    rewrite N.shiftl_spec_low by assumption. apply Bool.andb_false_r.
    erewrite bound_hibits_zero. reflexivity. apply getmem_bound. assumption.
Qed.

Lemma getbyte':
  forall len m a, a mod 4 <= len ->
  getmem 32 LittleE (N.succ len) m (a ⊖ a mod 4) .| N.ones (a mod 4 * 8) .& (N.ones 8 << (8*len)) =
  m Ⓑ[a ⊖ a mod 4+len] << (8*len).
Proof.
  intros. rewrite N.land_lor_distr_l. rewrite getbyte. replace (_.&_) with 0. apply N.lor_0_r.
  symmetry. apply N.bits_inj_0. intro b.
  rewrite N.land_spec. destruct (N.lt_ge_cases b (a mod 4 * 8)).
    rewrite N.shiftl_spec_low. apply Bool.andb_false_r. eapply N.lt_le_trans. eassumption.
      rewrite N.mul_comm. apply N.mul_le_mono_l, H.
    rewrite N.ones_spec_high. reflexivity. assumption.
Qed.

Lemma nonbyte:
  forall len m a, len < a mod 4 ->
  getmem 32 LittleE (N.succ len) m (a ⊖ a mod 4) .| N.ones (a mod 4 * 8) .& (N.ones 8 << (8*len)) <> 0.
Proof.
  intros. intro H1. apply N.bits_inj_iff in H1. specialize (H1 (8*len)).
  revert H1. rewrite N.bits_0. apply Bool.not_false_iff_true.
  rewrite N.land_spec, N.lor_spec, (N.mul_comm _ 8).
  rewrite N.ones_spec_low, Bool.orb_true_r by (apply N.mul_lt_mono_pos_l; [ reflexivity | assumption ]).
  rewrite N.shiftl_spec_high', N.sub_diag, N.ones_spec_low; reflexivity.
Qed.

Lemma nilfree_extend:
  forall j m p k (P32: p < 2^32) (J4: j <= 4)
         (NF: nilfree m p (4*k - p mod 4))
         (NN: forall i, i < j ->
              ((if k then getmem 32 LittleE (N.succ i) m (p ⊖ p mod 4) .| N.ones (p mod 4 * 8)
                     else getmem 32 LittleE (N.succ i) m (p ⊖ p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*i)) =? 0) = false),
  nilfree m p (j + 4*k - p mod 4).
Proof.
  intros. intros i LT.
  psimpl. destruct k as [|k].
    rewrite N.add_0_r in LT. apply N.lt_add_lt_sub_l in LT. specialize (NN _ LT).
    apply N.eqb_neq in NN. intro H. apply NN.
    rewrite getbyte'. psimpl. rewrite H. apply N.shiftl_0_l. apply N.le_add_r.
  destruct (N.lt_ge_cases i (4*N.pos k - p mod 4)) as [H1|H1]. apply NF. assumption.
  assert (H2: p mod 4 <= 4 * N.pos k). transitivity 4.
    apply N.lt_le_incl, N.mod_lt. discriminate 1.
    destruct k; discriminate.
  rewrite <- N.add_sub_assoc in LT by assumption.
  rewrite <- (N.sub_add _ _ H1) in LT. apply N.add_lt_mono_r in LT.
  specialize (NN _ LT). apply N.eqb_neq in NN. intro H'. apply NN.
  rewrite <- add_msub_swap, <- add_msub_assoc, getmem_mod_l, getbyte.
  rewrite <- N.add_assoc, <- (getmem_mod_l _ _ 1), <- ofZ_toZ, !toZ_add, toZ_msub, !toZ_sub by assumption.
  rewrite <- !toZ_msub, <- !toZ_add, ofZ_toZ. psimpl. rewrite H'. apply N.shiftl_0_l.
Qed.

Theorem nilterminate:
  forall j m p k (P32: p < 2^32) (J4: j < 4)
         (NF: nilfree m p (4*k - p mod 4))
         (NN: forall i, i < j ->
               ((if k then getmem 32 LittleE (N.succ i) m (p ⊖ p mod 4) .| N.ones (p mod 4 * 8)
                     else getmem 32 LittleE (N.succ i) m (p ⊖ p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*i)) =? 0) = false)
         (NIL: ((if k then getmem 32 LittleE (N.succ j) m (p ⊖ p mod 4) .| N.ones (p mod 4 * 8)
                      else getmem 32 LittleE (N.succ j) m (p ⊖ p mod 4 ⊕ 4*k)) .& (N.ones 8 << (8*j)) =? 0) = true),
  nilfree m p (j + 4*k ⊖ p mod 4) /\ m Ⓑ[j + p + 4*k ⊖ p mod 4] = 0.
Proof.
  intros. destruct N.land eqn:H in NIL; [|discriminate]. clear NIL. rename H into NIL.
  destruct (N.lt_ge_cases (4*k + j) (p mod 4)) as [JP1|JP1].

  (* Strlen never yields negative lengths despite rounding the pointer down to a word boundary,
     because it loads non-zero bytes into the buffer before the string starts. *)
  destruct k as [|k].
    contradict NIL. apply nonbyte. rewrite <- (N.add_0_l j). apply JP1.
    contradict JP1. apply N.nlt_ge. transitivity 4.
      apply N.lt_le_incl, N.mod_lt. discriminate 1.
      etransitivity; [|apply N.le_add_r]. destruct k; discriminate 1.

  destruct (N.lt_ge_cases (4*k + j) (2^32 + p mod 4)) as [JP2|JP2].

    (* Main proof: Termination of the main loop yields the correct length. *)
    split.
      unfold msub. psimpl. rewrite <- N.add_assoc, <- N.add_sub_assoc by
        (rewrite (N.add_comm j); assumption). psimpl.
        apply nilfree_mod, nilfree_extend; try assumption. apply N.lt_le_incl, J4.
      rewrite <- N.add_assoc, <- add_msub_assoc, N.add_comm, getmem_mod_l,
              <- (N.shiftr_0_l (8*j)), <- NIL. destruct k as [|k].
        rewrite getbyte', N.add_0_r by exact JP1.
          rewrite N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r; reflexivity.
        rewrite getbyte, (N.add_comm p), <- add_msub_assoc, (N.add_comm (4*_)).
          rewrite N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r; reflexivity.

    (* Weird special case:  Strlen never terminates after exceeding 2^32 bytes because
       at that point it is reading bytes previously recognized as non-nil (and it doesn't
       modify memory as it iterates). *)
    destruct k as [|k]. contradict JP2. apply N.nle_gt. eapply N.lt_le_trans.
      apply J4. etransitivity; [|apply N.le_add_r]. discriminate 1.
    specialize (NF (4*N.pos k + j - (2^32 + p mod 4))). exfalso. apply NF.
    apply N.lt_add_lt_sub_r. rewrite N.sub_add_distr, N.sub_add.
      eapply N.add_lt_mono_r. rewrite N.sub_add. apply N.add_lt_mono_l.
        transitivity 4. assumption. reflexivity.
        etransitivity; [|eassumption]. apply N.le_add_r.
      apply N.le_add_le_sub_l, JP2.
    rewrite getbyte, <- add_msub_swap, <- add_msub_assoc,
            <- getmem_mod_l, mp2_add_l, <- N.add_assoc, <- mp2_add_r, getmem_mod_l in NIL.
    apply N.shiftl_eq_0_iff in NIL. rewrite <- NIL.
    rewrite <- getmem_mod_l. rewrite <- mp2_add_r, <- msub_sub by assumption.
    rewrite <- add_msub_swap. psimpl. reflexivity.
Qed.


(* Main correctness theorem (and proof): *)
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

  Local Ltac step := time arm7_step.

  (* Precondition *)
  step. exact R0.

  (* Inductive cases *)
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

  (* Address 0 *)
  step. step. step. step.
    rewrite <- (N.ldiff_land_low _ 3 32) by (destruct p; [|apply N.log2_lt_pow2;[|apply (arm7_regsize MDL PRE)]]; reflexivity).
    change 3 with (N.ones 2). rewrite ldiff_sub, N.land_ones.
  step. exists 0.
    apply Neqb_ok in BC. rewrite BC. simpl N.succ. change (N.ones _) with 0. psimpl. repeat split.
    intros i LT. destruct i; discriminate.
  step. step.
    apply N.eqb_neq in BC.
    assert (LE1: 1 <= p mod 4). destruct (p mod _). contradict BC. reflexivity. destruct p0; discriminate.
    rewrite (proj2 (N.leb_le _ _) LE1).
    rewrite (msub_nowrap _ 1) at 2 by (psimpl; apply LE1). psimpl.
  step. step.
    apply Neqb_ok in BC0. rewrite BC0.
    replace (p-1) with (p⊖1); cycle 1.
      rewrite msub_nowrap; psimpl. reflexivity.
      etransitivity. apply LE1. apply N.mod_le. discriminate 1.
    psimpl.
  step. exists 0.
    rewrite BC0. simpl N.succ. psimpl. repeat split.
    intros i LT. destruct i; discriminate.
  step.
    apply N.eqb_neq in BC0.
    assert (LE2: 2 <= p mod 4).
      destruct (N.zero_one (p mod 4)) as [H|[H|H]]; [rewrite H in *; contradiction..|].
      change 2 with (N.succ 1). apply N.le_succ_l, H.
    rewrite (msub_nowrap _ 1) by (psimpl; transitivity 2; [ discriminate 1 | exact LE2 ]).
    rewrite (msub_nowrap _ 2) at 3 by (psimpl; exact LE2).
    replace (1 <=? _) with true by (symmetry; psimpl; apply N.leb_le, N.le_add_le_sub_r, LE2).
    replace (p - p mod 4) with (p ⊖ p mod 4) by
    ( rewrite msub_nowrap; psimpl; [ reflexivity | apply N.mod_le; discriminate 1 ] ).
    psimpl.
  step.
    exists 0.
      apply Neqb_ok in BC1. rewrite BC1, <- N.lor_assoc. simpl N.succ. psimpl. repeat split.
      intros i LT. destruct i; discriminate.
    exists 0. replace (p mod 4) with 3.
      rewrite <- !N.lor_assoc. simpl N.succ. psimpl. repeat split. intros i LT. destruct i; discriminate.
      assert (LT3: p mod 4 < 4). apply N.mod_lt. discriminate.
      destruct (p mod 4). contradiction. repeat (discriminate + destruct p0). reflexivity. contradiction.

  (* Address 40 *)
  destruct PRE as [k [R0 [R1 [R2 NF]]]].
  repeat (discriminate + step).

    (* nil at offset 4k+0 *)
    rewrite <- N.land_ones in BC0.
    eexists. split. reflexivity. psimpl.
    rewrite <- (N.add_0_l (4*k)), N.add_assoc, (N.add_comm p 0).
    apply nilterminate; try assumption. reflexivity.
      intros i LT. destruct i; discriminate LT.
      simpl N.succ. psimpl. assumption.

    (* nil at offset 4k+1 *)
    rewrite <- N.land_ones in BC1.
    eexists. split. reflexivity. psimpl. apply nilterminate; simpl N.succ; psimpl; try assumption. reflexivity.
    intros i LT. destruct i as [|i]. simpl N.succ. psimpl. assumption. destruct i; discriminate LT.

    (* nil at offset 4k+2 *)
    rewrite <- N.land_ones in BC2.
    eexists. split. reflexivity. psimpl. apply nilterminate; simpl N.succ; psimpl; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT || (simpl N.succ; psimpl; assumption) || destruct i as [i|i|]).

    (* nil at offset 4k+3 *)
    rewrite <- N.land_ones in BC3.
    eexists. split. reflexivity. psimpl. apply nilterminate; simpl N.succ; psimpl; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT || (simpl N.succ; psimpl; assumption) || destruct i as [i|i|]).

    (* no nils from 4k+0 to 4k+3: iterate loop *)
    rewrite <- N.land_ones in BC.
    exists (1+k). rewrite !N.mul_succ_r, N.mul_add_distr_l. psimpl. repeat split.
    eapply nilfree_extend; try assumption. reflexivity.
    intros i LT. destruct i as [|i]; repeat (discriminate LT || (simpl N.succ; psimpl; assumption) || destruct i as [i|i|]).
Qed.
