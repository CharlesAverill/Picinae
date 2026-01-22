Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import Picinae_armv7.
Require Import arm7_memset.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

(* The ARM7 lifter creates non-writable code sections. *)
Theorem memset_nwc: forall s2 s1, memset_arm s1 = memset_arm s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem memset_welltyped: welltyped_prog arm7typctx memset_arm.
Proof.
  Picinae_typecheck.
Qed.

Definition memset_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 120 => true
  | _ => false
  end | _ => false end.

(* Correctness specification:  memset yields a memory state identical to
   starting memory m except with addresses p..p+len-1 filled with byte c.
   It also returns p in register r0. *)
Definition filled m p c len :=
  N.recursion m (fun i m' => m'[Ⓑ p+i := c]) len.

Definition postcondition m p c len s :=
  s R_R0 = p /\ s V_MEM32 = filled m p c len.


(* Invariants: *)

Definition regs (s:store) m p c len r0 r1 r2 :=
  s V_MEM32 = filled m p c len /\ s R_R0 = r0 /\ s R_R1 = r1 /\ s R_R2 = r2.

Definition common_inv p c len s m r1 k :=
  regs s m p c k p r1 (len ⊖ k) /\
  s R_R3 = p ⊕ k /\ k <= len.

Definition low8_pad c :=
  c .| c << 8 .| ((c .| c << 8) << 16) mod 2^32.

Definition memset_invset m p c len (t:trace) :=
  match t with (Addr a,s)::_ => match a with

  (* Entry point *)
  | 0 => Some (regs s m p c 0 p c len)

  (* Loop 1 (1-byte writes to word boundary) *)
  | 12 => Some (∃ k, common_inv p c len s m c k /\ 8 <= len /\ p mod 4 + k <= 4)

  (* Loop 2 (word aligned 8-byte writes) *)
  | 44 => Some (∃ k, common_inv p c len s m (low8_pad (c mod 2^8)) k /\ s R_R12 = s R_R1)

  (* Loop 3 (1-byte writes to end) *)
  | 84 => Some (∃ k r1, common_inv p c len s m r1 k /\ r1 mod 2^8 = c mod 2^8)

  (* post-condition: *)
  | 120 => Some (postcondition m p c len s)

  | _ => None
  end | _ => None end.


(* Supporting lemmas: *)

(* Filling 0 bytes leaves memory unchanged. *)
Lemma filled0: ∀ m p c, filled m p c 0 = m.
Proof.
  intros. reflexivity.
Qed.

(* Writing one more byte increments the filled length. *)
Lemma filled_succ:
  ∀ m p c k, (filled m p c k)[Ⓑp+k := c] = filled m p c (N.succ k).
Proof.
  intros. unfold filled. rewrite N.recursion_succ; try reflexivity.
  intros i j H m1 m2 H'. subst. reflexivity.
Qed.

Lemma filled_mod:
  ∀ m p c, filled m p (c mod 2^8) = filled m p c.
Proof.
  intros. extensionality len. unfold filled. apply f_equal2.
    extensionality i. extensionality m'. change 8 with (8*1). apply setmem_mod_r.
    reflexivity.
Qed. 

(* Writing n more bytes with a bounds-check on each index safely extends the
   filled length by n. *)
Fixpoint fill_n_more m p c n :=
  match n with O => m | S n' => fill_n_more m p c n' [ⒷN.of_nat n' + p := c] end.

Lemma filled_n_more:
  forall n len m p c k
    (KLEN: k <= len)
    (LEN32: len < 2^32)
    (BC: forall i, i < N.of_nat n -> (1 <=? len ⊖ k ⊖ i) = true)
    (BC': (1 <=? len ⊖ k ⊖ N.of_nat n) = false),
  fill_n_more (filled m p c k) (p+k) c n = filled m p c len.
Proof.
  induction n; intros.

    rewrite msub_0_r, msub_mod_pow2, N.min_id in BC'.
    apply N.leb_gt, N.lt_1_r, msub_move_0_r in BC'.
    rewrite !N.mod_small in BC'. rewrite BC'. reflexivity.
      eapply N.le_lt_trans; eassumption.
      assumption.

    rewrite Nat2N.inj_succ in BC,BC'.
    rewrite <- msub_add_distr in BC'. apply N.leb_gt, N.lt_1_r, msub_move_0_r in BC'.
    rewrite (N.mod_small _ _ LEN32) in BC'. subst len. psimpl in BC.
    assert (KN: k + N.succ (N.of_nat n) < 2^32).
      destruct (N.le_gt_cases (2^32) (N.succ (N.of_nat n))) as [H1|H1].
        specialize (BC (N.succ (N.of_nat n) mod 2^32)). psimpl in BC. discriminate BC.
        eapply N.lt_le_trans. apply mp2_mod_lt. apply H1.
      clear LEN32 BC IHn m p c. apply N.nle_gt. intro H.
      assert (K32: k < 2^32). eapply N.le_lt_trans. exact KLEN. apply mp2_mod_lt.
      contradict KLEN. apply N.nle_gt.
      rewrite <- msub_0_r, <- (N.Div0.mod_same (2^32)), msub_mod_r by reflexivity.
      rewrite (msub_sub _ _ _ H), N.mod_small;
          apply N.le_succ_l; rewrite <- N.sub_succ_l by assumption; apply N.le_sub_le_add_r.
        rewrite <- N.add_succ_r. apply N.add_le_mono_l, N.le_succ_l. assumption.
        apply N.le_succ_l, N.add_lt_mono; assumption.
    cbn [fill_n_more].
    rewrite (N.add_comm _ (p+k)), <- N.add_assoc.
    erewrite IHn, filled_succ.
      rewrite (N.mod_small _ _ KN), N.add_succ_r. reflexivity.
      apply N.le_add_r.
      etransitivity. apply N.lt_succ_diag_r. rewrite <- N.add_succ_r. apply KN.
      intros i H. specialize (BC (i⊕1)). rewrite <- N.add_1_l in BC. psimpl in BC. psimpl. apply BC.
        eapply N.le_lt_trans. apply mp2_mod_le. apply N.add_lt_mono_l, H.
      psimpl. reflexivity.
Qed.

(* Writing 4 more bytes as a single 32-bit word increases the filled length by 4. *)
Lemma filled4:
  ∀ m p c k,
  filled m p c k [Ⓓp+k := low8_pad (c mod 2^8)] = filled m p c (4+k).
Proof.
  intros. rewrite <- filled_mod. change 4 with (1+(1+(1+1))). rewrite !setmem_split.
  unshelve (repeat (
    match goal with |- context [ setmem _ _ 1 (filled _ _ ?y _) _ ?x ] => replace x with y by shelve end;
    rewrite filled_succ, <- 1?N.add_1_r, <- 1?(N.add_assoc p) by apply mp2_mod_lt
  )); unfold low8_pad.

  psimpl. reflexivity.
  rewrite !N.shiftr_lor. psimpl. reflexivity.
  rewrite !N.shiftr_lor. psimpl. reflexivity.
  psimpl. rewrite !N.shiftr_lor, !N.shiftl_lor, <- (N.land_ones _ 32), N.shiftr_land.
    simpl (N.ones _ >> _). rewrite N.shiftr_lor. psimpl. reflexivity.

  rewrite (N.add_comm _ k), !N.add_assoc. reflexivity.
Qed.

(* Prove that using 3-bit binary arithmetic to compute absolute differences of
   small signed numbers is a sound optimization. *)
Lemma abs_diff:
  ∀ i len k, (8 <=? len ⊖ k ⊖ 8*i) = false -> msub 3 len k = len ⊖ 8*i ⊖ k.
Proof.
  intros.
  replace (msub 3 len k) with (msub 3 len (8*i+k)) by (psimpl; reflexivity).
  change 3 with (N.min 32 3). rewrite <- msub_mod_pow2, N.mod_small; psimpl.
    reflexivity.
    rewrite msub_comm. apply N.leb_gt, H.
Qed.

(* Prove that the code's method of checking in-bounds writes is sound. *)
Lemma checked_add_true:
  ∀ n k len (KLEN: k <= len) (LEN32: len < 2^32) (BC: (n <=? len ⊖ k) = true),
  k + n <= len.
Proof.
  intros.
  rewrite N.add_comm. rewrite <- (N.sub_add _ _ KLEN). apply N.add_le_mono_r.
  rewrite <- (N.mod_small _ _ LEN32). rewrite <- (N.mod_small k (2^32)).
    rewrite <- msub_nowrap.
      apply N.leb_le, BC.
      rewrite (N.mod_small _ _ LEN32). etransitivity. apply mp2_mod_le. apply KLEN.
    eapply N.le_lt_trans; eassumption.
Qed.

(* Prove that the code's method of detecting loop-end through integer underflow is sound. *)
Lemma checked_add_lt:
  ∀ k n len (NLO: n <= 2^31) (KLEN: k <= len) (LEN32: len < 2^32) (BC: len ⊖ (k + n) < n),
  n + k <= len.
Proof.
  intros. apply N.nlt_ge. intro H. contradict BC. apply N.nlt_ge.
  etransitivity. apply NLO.
  apply le_msub_iff. rewrite (N.mod_small _ _ LEN32).
  destruct (N.lt_ge_cases (k+n) (2^32)) as [H1|H1].
    right. rewrite (N.mod_small _ _ H1). split.
      rewrite N.add_comm. exact H.
      rewrite <- N.add_assoc. rewrite N.add_comm. apply N.add_le_mono.
        change (2^32) with (2^31 + 2^31). apply N.add_le_mono_r, NLO.
        exact KLEN.
    left. replace (_ mod _) with (k+n-2^31-2^31).
      rewrite N.sub_add.
        apply N.le_sub_le_add_r, N.add_le_mono; assumption.
        apply N.le_add_le_sub_l, H1.
      rewrite <- N.sub_add_distr. eapply N.add_cancel_r. rewrite N.sub_add.
        change (2^31+2^31) with (2^32). replace (2^32) with (2^32*((k+n)/2^32)) at 2.
          rewrite (N.add_comm (_ mod _)). apply N.div_mod'.
          change (2^32) with (2^32*1) at 3. apply f_equal, N.le_antisymm.
            change 1 with ((2^32+2^31)/2^32). apply N.Div0.div_le_mono, N.add_le_mono.
              etransitivity. exact KLEN. apply N.lt_le_incl, LEN32.
              exact NLO.
            change 1 with (2^32/2^32). apply N.Div0.div_le_mono, H1.
        exact H1.
Qed.

Corollary checked_add_false:
  forall n k len (NLO: n <= 2^31) (NHI: 8 <= n) (KLEN: k <= len) (LEN32: len < 2^32)
    (BC: (8 <=? len ⊖ k ⊖ n) = false),
  n + k <= len.
Proof.
  intros. apply checked_add_lt; try assumption.
  eapply N.lt_le_trans. rewrite msub_add_distr. apply N.leb_gt. exact BC. exact NHI.
Qed.


(* Main functional correctness proof: *)

Theorem memset_functional_correctness:
  ∀ s p c len mem t s' x'
    (ENTRY: startof t (x',s') = (Addr 0, s))
    (MDL: models arm7typctx s)
    (MEM: s V_MEM32 = mem) (R0: s R_R0 = p) (R1: s R_R1 = c) (R2: s R_R2 = len),
  satisfies_all memset_arm (memset_invset mem p c len) memset_exit ((x',s')::t).
Proof.
  (* Report time to interpret each instruction: *)
  Local Ltac step := time arm7_step.

  (* Start proof by induction: *)
  intros. apply prove_invs.

  (* Base case: *)
  simpl. rewrite ENTRY. step. rewrite filled0. repeat split; assumption.

  (* Change assumptions about s into assumptions about s1. *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  assert (LEN32 := models_var R_R2 MDL). rewrite R2 in LEN32. unfold arm7typctx in LEN32.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1 LEN32. rename t1 into t. rename s1 into s. rename MDL1 into MDL.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 32 PRE.

  (* Entry point (address 0) *)
  destruct PRE as [MEM [R0 [R1 R2]]].
  step. step. step.
  exists 0. repeat eexists; psimpl; try (eassumption || reflexivity).
    apply N.le_0_l.
    apply N.leb_le, BC.
    apply N.lt_le_incl, (mp2_mod_lt p 2).
  exists 0. repeat eexists; psimpl; try (eassumption || reflexivity).
    apply N.le_0_l.
    rewrite R1. reflexivity.

  (* Loop 1 (address 12) *)
  destruct PRE as [k [[[MEM [R0 [R1 R2]]] [R3 KLEN]] [LEN8 KP4]]].
  step. step. step. step.

    (* end loop 1 *)
    repeat step. repeat eexists; psimpl; try eassumption.
      unfold low8_pad. psimpl. reflexivity.

    (* iterate loop 1 *)
    step. step. exists (k⊕1). repeat eexists; psimpl; try (eassumption || reflexivity).
      rewrite N.add_1_r, (N.mod_small (N.succ k)). apply filled_succ.
        eapply N.le_lt_trans. apply -> N.succ_le_mono. etransitivity. apply N.le_add_l. apply KP4. reflexivity.
      rewrite msub_comm. reflexivity.
      etransitivity. apply mp2_mod_le.
        rewrite N.add_1_l. apply N.le_succ_l.
        eapply N.add_lt_mono_l. eapply N.le_lt_trans. apply KP4.
        eapply (N.lt_le_trans _ 8). reflexivity.
        etransitivity. apply LEN8. apply N.le_add_l.
      apply N.le_lteq in KP4. destruct KP4 as [KP4|KP4].
        etransitivity.
          apply N.add_le_mono_l. apply mp2_mod_le.
          rewrite N.add_1_l, N.add_succ_r. apply N.le_succ_l, KP4.
        rewrite <- N.Div0.add_mod_idemp_l in BC. rewrite KP4 in BC. discriminate BC.

  (* Loop 2 (address 44) *)
  destruct PRE as [k [[[MEM [R0 [R1 R2]]] [R3 KLEN]] R12]]. rewrite R1 in R12.
  step. step; cycle 1.

    (* end loop 2 (1st exit point) *)
    repeat step. exists k. repeat eexists; psimpl; try assumption.
      rewrite (abs_diff 0); psimpl. reflexivity. assumption.
      unfold low8_pad. psimpl. reflexivity.

    (* end loop 2 (2nd exit point) *)
    step. step; cycle 1. repeat step.
    eassert (H:_). apply (checked_add_false 8); (discriminate 1 || eassumption).
    exists (8⊕k). repeat eexists; psimpl; try (assumption || reflexivity).
      repeat rewrite filled4, ?N.add_assoc, 1?(N.add_comm _ p), <- 1?(N.add_assoc p).
        rewrite (N.mod_small (8+k)). reflexivity.
        eapply N.le_lt_trans; eassumption.
      rewrite (abs_diff 1). reflexivity. assumption.
      etransitivity. apply mp2_mod_le. assumption.
      unfold low8_pad. psimpl. reflexivity.

    (* end loop 2 (3rd exit point) *)
    step. step; cycle 1. repeat step.
    eassert (H:_). apply (checked_add_false 16); (discriminate 1 || eassumption).
    exists (16⊕k). repeat eexists; psimpl; try (assumption || reflexivity).
      repeat rewrite filled4, ?N.add_assoc, 1?(N.add_comm _ p), <- 1?(N.add_assoc p).
        rewrite (N.mod_small (16+k)). reflexivity.
        eapply N.le_lt_trans; eassumption.
      rewrite (abs_diff 2). reflexivity. assumption.
      etransitivity. apply mp2_mod_le. assumption.
      unfold low8_pad. psimpl. reflexivity.

    (* end loop 2 (4th exit point) *)
    step. step; cycle 1. repeat step.
    eassert (H:_). apply (checked_add_false 24); (discriminate 1 || eassumption).
    exists (24⊕k). repeat eexists; psimpl; try (assumption || reflexivity).
      repeat rewrite filled4, ?N.add_assoc, 1?(N.add_comm _ p), <- 1?(N.add_assoc p).
        rewrite (N.mod_small (24+k)). reflexivity.
        eapply N.le_lt_trans; eassumption.
      rewrite (abs_diff 3). reflexivity. assumption.
      etransitivity. apply mp2_mod_le. assumption.
      unfold low8_pad. psimpl. reflexivity.

    (* iterate loop 2 *)
    step.
    assert (H: 32 + k <= len).
      rewrite <- msub_add_distr in BC0,BC1,BC2. rewrite N.add_comm. change 32 with (8+8+8+8).
      repeat (rewrite 1?N.add_assoc; apply checked_add_true; try assumption).
    exists (32⊕k). repeat eexists; psimpl; try (assumption || reflexivity).
      repeat rewrite filled4, ?N.add_assoc, 1?(N.add_comm _ p), <- 1?(N.add_assoc p).
        rewrite (N.mod_small (32+k)). reflexivity.
        eapply N.le_lt_trans; eassumption.
      rewrite msub_comm. reflexivity.
      etransitivity. apply mp2_mod_le. assumption.

  (* Loop 3 (address 84) *)
  destruct PRE as [k [r1 [[[MEM [R0 [R1 R2]]] [R3 KLEN]] R1C]]].

    (* end loop 3 (1st exit point) *)
    step. step; cycle 1.
    repeat step. split. assumption. psimpl.
      apply (filled_n_more 0%nat len); try assumption.
        intros i H. contradict H. apply N.nlt_0_r.
        rewrite msub_0_r, msub_mod_pow2. assumption.

    (* end loop 3 (2nd exit point) *)
    step. step; cycle 1.
    repeat step. split. assumption. psimpl.
      rewrite <- !(setmem_mod_r _ _ _ _ _ r1). change (1*8) with 8. rewrite R1C, !setmem_mod_r.
      apply (filled_n_more 1%nat len); try assumption.
        intros i H. apply N.lt_1_r in H. rewrite H, msub_0_r, msub_mod_pow2. assumption.

    (* end loop 3 (3rd exit point) *)
    step. step; cycle 1.
    repeat step. split. assumption. psimpl.
      rewrite <- !(setmem_mod_r _ _ _ _ _ r1). change (1*_) with 8. rewrite R1C, !setmem_mod_r.
      rewrite <- (N.add_assoc 1). apply (filled_n_more 2%nat len); try assumption.
        intros i H. apply (N.lt_succ_r _ 1), N.le_1_r in H. destruct H; subst i.
          rewrite msub_0_r, msub_mod_pow2. assumption.
          assumption.

    (* end loop 3 (4th exit point) *)
    step. step; cycle 1.
    repeat step. split. assumption. psimpl.
      rewrite <- !(setmem_mod_r _ _ _ _ _ r1). change (1*_) with 8. rewrite R1C, !setmem_mod_r.
      rewrite <- !(N.add_assoc _ p k). apply (filled_n_more 3%nat len); try assumption.
        intros i H. apply (N.lt_succ_r _ 2), N.le_lteq in H. destruct H.
          apply (N.lt_succ_r _ 1), N.le_1_r in H. destruct H; subst i.
            rewrite msub_0_r, msub_mod_pow2. assumption.
            assumption.
          subst i. assumption.

    (* iterate loop 3 *)
    step. exists (4⊕k).
    assert (K4LEN: 4+k <= len).
      rewrite <- msub_add_distr in BC0,BC1,BC2. rewrite N.add_comm. change 4 with (1+1+1+1).
      repeat (rewrite 1?N.add_assoc; apply checked_add_true; try assumption).
    repeat eexists; psimpl; try (assumption || reflexivity).
      rewrite <- !(setmem_mod_r _ _ _ _ _ r1). change (1*_) with 8. rewrite R1C, !setmem_mod_r.
        change (2+p) with (1+1+p). change (3+p) with (1+1+1+p).
        rewrite <- !(N.add_assoc 1), !N.add_1_l, <- !N.add_succ_r.
        rewrite !filled_succ by apply mp2_mod_lt.
        rewrite <- !N.add_1_l, !N.add_assoc. rewrite (N.mod_small (4+k)). reflexivity.
        eapply N.le_lt_trans. apply K4LEN. apply LEN32.
      rewrite msub_comm. reflexivity.
      etransitivity. apply mp2_mod_le. apply K4LEN.
Qed.
