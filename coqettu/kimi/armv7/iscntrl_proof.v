(* iscntrl -- test for an ASCII control character

   SEMANTICS
   ---------
   The first comparison tests for DEL (0x7f).  A conditional second comparison
   tests whether the input is at most 0x1f, and the final ITE pair returns one
   for either case and zero otherwise.

   SPECIFICATION (ISO C / POSIX iscntrl)
   -------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int iscntrl(int c);

     DESCRIPTION
            iscntrl() tests whether c is a control character.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            iscntrl at ELF VA 0x3d985 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d984.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see iscntrl_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d984.
   Output:  At BX LR at 0x4d990, R0 = 1 when c = 0x7f or c <= 0x1f, and zero
            otherwise.  Memory, SP, LR, and callee-saved registers are
            unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import iscntrl_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition iscntrl_entry : addr := 0x4d984.
Definition iscntrl_return : addr := 0x4d990.

Definition iscntrl_test (x : N) : bool := (x =? 0x7f) || (x <=? 0x1f).
Definition iscntrl_zero (x : N) : bool := (x =? 0x7f) || (x =? 0x1f).

Lemma iscntrl_test_of_carry x :
  (0x1f <=? x) = true -> iscntrl_test x = iscntrl_zero x.
Proof.
  intros H. apply N.leb_le in H.
  destruct (x =? 0x1f) eqn:E.
  - apply N.eqb_eq in E. subst x. reflexivity.
  - pose proof (proj1 (N.eqb_neq x 0x1f) E) as NE.
    unfold iscntrl_test, iscntrl_zero. rewrite E, !Bool.orb_false_r.
    replace (x <=? 0x1f) with false by (symmetry; apply N.leb_gt; lia).
    rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma iscntrl_test_of_no_carry x :
  (0x1f <=? x) = false -> iscntrl_test x = true.
Proof.
  intros H. apply N.leb_gt in H.
  unfold iscntrl_test.
  replace (x <=? 0x1f) with true by (symmetry; apply N.leb_le; lia).
  apply Bool.orb_true_r.
Qed.

Definition iscntrl_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition iscntrl_first (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_CF = (if 0x7f <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if s0 R_R0 =? 0x7f then 1 else 0) /\
  iscntrl_frame s0 s.

Definition iscntrl_flags (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_CF = (if 0x1f <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if iscntrl_zero (s0 R_R0) then 1 else 0) /\
  iscntrl_frame s0 s.

Definition iscntrl_mid (s0 s : store) : Prop :=
  s R_R0 = (if iscntrl_test (s0 R_R0) then 1 else s0 R_R0) /\
  s R_CF = (if 0x1f <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if iscntrl_zero (s0 R_R0) then 1 else 0) /\
  iscntrl_frame s0 s.

Definition iscntrl_post (s0 s : store) : Prop :=
  s R_R0 = (if iscntrl_test (s0 R_R0) then 1 else 0) /\
  iscntrl_frame s0 s.

Definition iscntrl_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d984 => Some (s = s0)
      | 0x4d986 | 0x4d988 => Some (iscntrl_first s0 s)
      | 0x4d98a | 0x4d98c => Some (iscntrl_flags s0 s)
      | 0x4d98e => Some (iscntrl_mid s0 s)
      | 0x4d990 => Some (iscntrl_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition iscntrl_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? iscntrl_return
  | _ => false
  end.

Theorem iscntrl_nwc : forall s1 s2, iscntrl_armv7 s1 = iscntrl_armv7 s2.
Proof. reflexivity. Qed.

Theorem iscntrl_welltyped : welltyped_prog arm7typctx iscntrl_armv7.
Proof. exact welltyped. Qed.

Theorem iscntrl_preserves_memory :
  forall_endstates iscntrl_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem iscntrl_preserves_lr :
  forall_endstates iscntrl_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem iscntrl_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates iscntrl_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem iscntrl_correct :
  forall prog (EXT : iscntrl_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr iscntrl_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (iscntrl_invs s0) iscntrl_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := iscntrl_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold iscntrl_invs.
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
        apply iscntrl_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold iscntrl_first, iscntrl_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold iscntrl_first, iscntrl_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold iscntrl_first, iscntrl_frame.
        elimstore. repeat split; assumption.

      * unfold iscntrl_first, iscntrl_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (s0 R_R0 =? 0x7f) eqn:E127.
        -- apply N.eqb_eq in E127. simpl in ZF. arm7_step.
           unfold iscntrl_flags, iscntrl_frame, iscntrl_zero. rewrite E127 in *.
           elimstore. repeat split; psimpl; reflexivity.
        -- simpl in ZF. arm7_step.
           unfold iscntrl_flags, iscntrl_frame, iscntrl_zero. rewrite ?E127.
           elimstore. repeat split; psimpl; try assumption; try reflexivity;
             rewrite ?Bool.orb_false_l, ?N.mod_small by assumption; reflexivity.

      * unfold iscntrl_flags, iscntrl_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold iscntrl_flags, iscntrl_frame.
        elimstore. repeat split; assumption.

      * unfold iscntrl_flags, iscntrl_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (0x1f <=? s0 R_R0) eqn:HCF; simpl in CF.
        -- pose proof (iscntrl_test_of_carry _ HCF) as HT.
           destruct (iscntrl_zero (s0 R_R0)) eqn:HZ; simpl in ZF; arm7_step;
             unfold iscntrl_mid, iscntrl_frame; rewrite HT, HZ, HCF;
             elimstore; repeat split; psimpl; try assumption; reflexivity.
        -- pose proof (iscntrl_test_of_no_carry _ HCF) as HT.
           arm7_step.
           unfold iscntrl_mid, iscntrl_frame. rewrite HT, HCF.
           elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold iscntrl_mid, iscntrl_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (0x1f <=? s0 R_R0) eqn:HCF; simpl in CF.
        -- pose proof (iscntrl_test_of_carry _ HCF) as HT.
           destruct (iscntrl_zero (s0 R_R0)) eqn:HZ; simpl in ZF;
             rewrite HT in R0; simpl in R0; arm7_step;
             unfold iscntrl_post, iscntrl_frame; rewrite HT;
             elimstore; repeat split; psimpl; try assumption; reflexivity.
        -- pose proof (iscntrl_test_of_no_carry _ HCF) as HT.
           rewrite HT in R0. simpl in R0. arm7_step.
           unfold iscntrl_post, iscntrl_frame. rewrite HT.
           elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
