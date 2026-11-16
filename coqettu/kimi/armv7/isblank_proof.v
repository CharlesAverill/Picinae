(* isblank -- test for ASCII tab or space

   SEMANTICS
   ---------
   The first comparison tests for tab (0x09).  A conditional second comparison
   tests for space (0x20), and the final ITE pair returns one for either value
   and zero otherwise.

   SPECIFICATION (ISO C / POSIX isblank)
   ------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int isblank(int c);

     DESCRIPTION
            isblank() tests whether c is a blank character: space or tab.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isblank at ELF VA 0x3d973 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d972.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isblank_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d972.
   Output:  At BX LR at 0x4d97e, R0 = 1 when c = 0x09 or c = 0x20, and zero
            otherwise.  Memory, SP, LR, and callee-saved registers are
            unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import isblank_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition isblank_entry : addr := 0x4d972.
Definition isblank_return : addr := 0x4d97e.

Definition isblank_test (x : N) : bool := (x =? 0x9) || (x =? 0x20).

Definition isblank_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isblank_first (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_ZF = (if s0 R_R0 =? 0x9 then 1 else 0) /\
  isblank_frame s0 s.

Definition isblank_flags (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_ZF = (if isblank_test (s0 R_R0) then 1 else 0) /\
  isblank_frame s0 s.

Definition isblank_mid (s0 s : store) : Prop :=
  s R_R0 = (if isblank_test (s0 R_R0) then 1 else s0 R_R0) /\
  s R_ZF = (if isblank_test (s0 R_R0) then 1 else 0) /\
  isblank_frame s0 s.

Definition isblank_post (s0 s : store) : Prop :=
  s R_R0 = (if isblank_test (s0 R_R0) then 1 else 0) /\
  isblank_frame s0 s.

Definition isblank_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d972 => Some (s = s0)
      | 0x4d974 | 0x4d976 => Some (isblank_first s0 s)
      | 0x4d978 | 0x4d97a => Some (isblank_flags s0 s)
      | 0x4d97c => Some (isblank_mid s0 s)
      | 0x4d97e => Some (isblank_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isblank_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? isblank_return
  | _ => false
  end.

Theorem isblank_nwc : forall s1 s2, isblank_armv7 s1 = isblank_armv7 s2.
Proof. reflexivity. Qed.

Theorem isblank_welltyped : welltyped_prog arm7typctx isblank_armv7.
Proof. exact welltyped. Qed.

Theorem isblank_preserves_memory :
  forall_endstates isblank_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isblank_preserves_lr :
  forall_endstates isblank_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isblank_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isblank_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isblank_correct :
  forall prog (EXT : isblank_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isblank_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isblank_invs s0) isblank_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isblank_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isblank_invs.
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
        apply isblank_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isblank_first, isblank_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isblank_first, isblank_frame in PRE.
        destruct PRE as (R0 & ZF & MEM & SP & LR).
        arm7_step.
        unfold isblank_first, isblank_frame.
        elimstore. repeat split; assumption.

      * unfold isblank_first, isblank_frame in PRE.
        destruct PRE as (R0 & ZF & MEM & SP & LR).
        destruct (s0 R_R0 =? 0x9) eqn:E9.
        -- simpl in ZF. arm7_step.
           unfold isblank_flags, isblank_frame, isblank_test. rewrite ?E9.
           elimstore. repeat split; psimpl; try assumption; try reflexivity;
             rewrite ?Bool.orb_true_l, ?Bool.orb_true_r,
                     ?Bool.orb_false_l, ?Bool.orb_false_r,
                     ?N.mod_small by assumption; reflexivity.
        -- simpl in ZF. arm7_step.
           unfold isblank_flags, isblank_frame, isblank_test. rewrite ?E9.
           elimstore. repeat split; psimpl; try assumption; try reflexivity;
             rewrite ?Bool.orb_true_l, ?Bool.orb_true_r,
                     ?Bool.orb_false_l, ?Bool.orb_false_r,
                     ?N.mod_small by assumption; reflexivity.

      * unfold isblank_flags, isblank_frame in PRE.
        destruct PRE as (R0 & ZF & MEM & SP & LR).
        arm7_step.
        unfold isblank_flags, isblank_frame.
        elimstore. repeat split; assumption.

      * unfold isblank_flags, isblank_frame in PRE.
        destruct PRE as (R0 & ZF & MEM & SP & LR).
        destruct (isblank_test (s0 R_R0)) eqn:ET; simpl in ZF; arm7_step;
          unfold isblank_mid, isblank_frame; rewrite ET;
          elimstore; repeat split; psimpl; try assumption; reflexivity.

      * unfold isblank_mid, isblank_frame in PRE.
        destruct PRE as (R0 & ZF & MEM & SP & LR).
        destruct (isblank_test (s0 R_R0)) eqn:ET; simpl in ZF; arm7_step;
          unfold isblank_post, isblank_frame; rewrite ET;
          elimstore; repeat split; psimpl; try assumption; reflexivity.
Qed.
