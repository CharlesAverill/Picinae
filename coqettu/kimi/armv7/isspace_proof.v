(* isspace -- test for ASCII whitespace

   SEMANTICS
   ---------
   The function forms c - 9, separately tests for space (0x20), and otherwise
   tests whether the modular difference is at most four.  Thus it recognizes
   tab through carriage return and space.

   SPECIFICATION (ISO C / POSIX isspace)
   -------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int isspace(int c);

     DESCRIPTION
            isspace() tests whether c is a whitespace character.  The theorem
            specifies exact full-register behavior, including modular subtraction.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isspace at ELF VA 0x3d9f7 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d9f6.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isspace_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d9f6.
   Output:  At BX LR at 0x4da06, R0 = 1 when c = 0x20 or
            (c - 9) mod 2^32 <= 4, and zero otherwise.  Memory, SP, LR, and
            callee-saved registers are unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isspace_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition isspace_entry : addr := 0x4d9f6.
Definition isspace_return : addr := 0x4da06.

Definition isspace_test (x : N) : bool :=
  (x =? 0x20) || ((x ⊖ 0x9) <=? 0x4).
Definition isspace_zero (x : N) : bool :=
  (x =? 0x20) || ((x ⊖ 0x9) =? 0x4).
Definition isspace_carry (x : N) : bool :=
  (x =? 0x20) || (0x4 <=? (x ⊖ 0x9)).

Lemma isspace_test_of_carry x :
  isspace_carry x = true -> isspace_test x = isspace_zero x.
Proof.
  intros H. destruct (x =? 0x20) eqn:E32.
  - apply N.eqb_eq in E32. subst x. reflexivity.
  - unfold isspace_carry in H. rewrite E32, Bool.orb_false_l in H.
    apply N.leb_le in H. unfold isspace_test, isspace_zero.
    rewrite E32, !Bool.orb_false_l.
    destruct ((x ⊖ 0x9) =? 0x4) eqn:E4.
    + apply N.eqb_eq in E4. rewrite E4. reflexivity.
    + pose proof (proj1 (N.eqb_neq (x ⊖ 0x9) 0x4) E4) as NE.
      replace ((x ⊖ 0x9) <=? 0x4) with false by
        (symmetry; apply N.leb_gt; lia).
      reflexivity.
Qed.

Lemma isspace_test_of_no_carry x :
  isspace_carry x = false -> isspace_test x = true.
Proof.
  intros H. unfold isspace_carry in H.
  apply Bool.orb_false_iff in H. destruct H as [_ H].
  apply N.leb_gt in H. unfold isspace_test.
  replace ((x ⊖ 0x9) <=? 0x4) with true by
    (symmetry; apply N.leb_le; lia).
  apply Bool.orb_true_r.
Qed.

Definition isspace_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isspace_sub_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x9 /\ isspace_frame s0 s.

Definition isspace_first (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x9 /\
  s R_CF = (if 0x20 <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if s0 R_R0 =? 0x20 then 1 else 0) /\
  isspace_frame s0 s.

Definition isspace_flags (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_CF = (if isspace_carry (s0 R_R0) then 1 else 0) /\
  s R_ZF = (if isspace_zero (s0 R_R0) then 1 else 0) /\
  isspace_frame s0 s.

Definition isspace_mid (s0 s : store) : Prop :=
  s R_R0 = (if isspace_test (s0 R_R0) then 1 else s0 R_R0) /\
  s R_CF = (if isspace_carry (s0 R_R0) then 1 else 0) /\
  s R_ZF = (if isspace_zero (s0 R_R0) then 1 else 0) /\
  isspace_frame s0 s.

Definition isspace_post (s0 s : store) : Prop :=
  s R_R0 = (if isspace_test (s0 R_R0) then 1 else 0) /\
  isspace_frame s0 s.

Definition isspace_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d9f6 => Some (s = s0)
      | 0x4d9fa => Some (isspace_sub_post s0 s)
      | 0x4d9fc | 0x4d9fe => Some (isspace_first s0 s)
      | 0x4da00 | 0x4da02 => Some (isspace_flags s0 s)
      | 0x4da04 => Some (isspace_mid s0 s)
      | 0x4da06 => Some (isspace_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isspace_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? isspace_return
  | _ => false
  end.

Theorem isspace_nwc : forall s1 s2, isspace_armv7 s1 = isspace_armv7 s2.
Proof. reflexivity. Qed.

Theorem isspace_welltyped : welltyped_prog arm7typctx isspace_armv7.
Proof. exact welltyped. Qed.

Theorem isspace_preserves_memory :
  forall_endstates isspace_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isspace_preserves_lr :
  forall_endstates isspace_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isspace_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isspace_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isspace_correct :
  forall prog (EXT : isspace_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isspace_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isspace_invs s0) isspace_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isspace_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isspace_invs.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - s0 MDL START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply isspace_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isspace_sub_post, isspace_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isspace_sub_post, isspace_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold isspace_first, isspace_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity;
          rewrite ?N.mod_small by assumption; reflexivity.

      * unfold isspace_first, isspace_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold isspace_first, isspace_frame.
        elimstore. repeat split; assumption.

      * unfold isspace_first, isspace_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        destruct (s0 R_R0 =? 0x20) eqn:E32.
        -- apply N.eqb_eq in E32. simpl in ZF. arm7_step.
           unfold isspace_flags, isspace_frame, isspace_carry, isspace_zero.
           rewrite E32 in *. elimstore. repeat split; psimpl; reflexivity.
        -- simpl in ZF. arm7_step.
           unfold isspace_flags, isspace_frame, isspace_carry, isspace_zero.
           rewrite ?E32. elimstore. repeat split; psimpl; try assumption;
             try reflexivity; rewrite ?Bool.orb_false_l, ?N.mod_small by assumption.
           pose proof (msub_eqb_spec (s0 R_R0) 0x9 0xd) as H.
           specialize (H (ltac:(lia)) (ltac:(lia))).
           change (((s0 R_R0) ⊖ 0x9 =? 0x4) =
                   (s0 R_R0 mod 2^32 =? 0xd)) in H.
           rewrite H, N.mod_small by assumption. reflexivity.

      * unfold isspace_flags, isspace_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold isspace_flags, isspace_frame.
        elimstore. repeat split; assumption.

      * unfold isspace_flags, isspace_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (isspace_carry (s0 R_R0)) eqn:HCF; simpl in CF.
        -- pose proof (isspace_test_of_carry _ HCF) as HT.
           destruct (isspace_zero (s0 R_R0)) eqn:HZ; simpl in ZF; arm7_step;
             unfold isspace_mid, isspace_frame; rewrite HT, HZ, HCF;
             elimstore; repeat split; psimpl; try assumption; reflexivity.
        -- pose proof (isspace_test_of_no_carry _ HCF) as HT.
           arm7_step.
           unfold isspace_mid, isspace_frame. rewrite HT, HCF.
           elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isspace_mid, isspace_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (isspace_carry (s0 R_R0)) eqn:HCF; simpl in CF.
        -- pose proof (isspace_test_of_carry _ HCF) as HT.
           destruct (isspace_zero (s0 R_R0)) eqn:HZ; simpl in ZF;
             rewrite HT in R0; simpl in R0; arm7_step;
             unfold isspace_post, isspace_frame; rewrite HT;
             elimstore; repeat split; psimpl; try assumption; reflexivity.
        -- pose proof (isspace_test_of_no_carry _ HCF) as HT.
           rewrite HT in R0. simpl in R0. arm7_step.
           unfold isspace_post, isspace_frame. rewrite HT.
           elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
