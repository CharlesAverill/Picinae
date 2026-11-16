(* isalnum -- test for an ASCII alphanumeric character

   SEMANTICS
   ---------
   ORR #0x20 folds ASCII case and an unsigned range test recognizes letters.
   Non-letters take a second unsigned range test for decimal digits.  Letters
   return one through an early branch; the digit path returns either zero or one.

   SPECIFICATION (ISO C / POSIX isalnum)
   -------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int isalnum(int c);

     DESCRIPTION
            isalnum() tests whether c is an alphanumeric character.  The theorem
            specifies exact full-register behavior, including modular arithmetic.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isalnum at ELF VA 0x3d937 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d936.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isalnum_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d936.
   Output:  At either BX LR, R0 = 1 when ((c OR 0x20) - 0x61) mod 2^32 <= 25
            or (c - 0x30) mod 2^32 <= 9, and zero otherwise.  Memory, SP, LR,
            and callee-saved registers are unchanged.  The proof stops before
            the return instruction.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isalnum_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition isalnum_entry : addr := 0x4d936.
Definition isalnum_return : addr := 0x4d94a.
Definition isalnum_early_return : addr := 0x4d94e.

Definition isalnum_alpha (x : N) : bool := (((x .| 0x20) ⊖ 0x61) <=? 0x19).
Definition isalnum_digit (x : N) : bool := ((x ⊖ 0x30) <=? 0x9).
Definition isalnum_test (x : N) : bool := isalnum_alpha x || isalnum_digit x.

Definition isalnum_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isalnum_orr_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) .| 0x20 /\ isalnum_frame s0 s.

Definition isalnum_sub_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = ((s0 R_R0) .| 0x20) ⊖ 0x61 /\
  isalnum_frame s0 s.

Definition isalnum_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = ((s0 R_R0) .| 0x20) ⊖ 0x61 /\
  s R_CF = (if 0x19 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61 then 1 else 0) /\
  s R_ZF = (if ((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x19 then 1 else 0) /\
  isalnum_frame s0 s.

Definition isalnum_digit_entry (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  isalnum_alpha (s0 R_R0) = false /\ isalnum_frame s0 s.

Definition isalnum_digit_sub_post (s0 s : store) : Prop :=
  s R_R0 = (s0 R_R0) ⊖ 0x30 /\
  isalnum_alpha (s0 R_R0) = false /\ isalnum_frame s0 s.

Definition isalnum_digit_cmp_post (s0 s : store) : Prop :=
  s R_R0 = (s0 R_R0) ⊖ 0x30 /\
  s R_CF = (if 0x9 <=? (s0 R_R0) ⊖ 0x30 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x30 =? 0x9 then 1 else 0) /\
  isalnum_alpha (s0 R_R0) = false /\ isalnum_frame s0 s.

Definition isalnum_mid (s0 s : store) : Prop :=
  s R_R0 = (if (s0 R_R0) ⊖ 0x30 <=? 0x9 then (s0 R_R0) ⊖ 0x30 else 0) /\
  s R_CF = (if 0x9 <=? (s0 R_R0) ⊖ 0x30 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x30 =? 0x9 then 1 else 0) /\
  isalnum_alpha (s0 R_R0) = false /\ isalnum_frame s0 s.

Definition isalnum_early (s0 s : store) : Prop :=
  isalnum_test (s0 R_R0) = true /\ isalnum_frame s0 s.

Definition isalnum_post (s0 s : store) : Prop :=
  s R_R0 = (if isalnum_test (s0 R_R0) then 1 else 0) /\
  isalnum_frame s0 s.

Definition isalnum_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d936 => Some (s = s0)
      | 0x4d93a => Some (isalnum_orr_post s0 s)
      | 0x4d93c => Some (isalnum_sub_post s0 s)
      | 0x4d93e => Some (isalnum_cmp_post s0 s)
      | 0x4d940 => Some (isalnum_digit_entry s0 s)
      | 0x4d942 => Some (isalnum_digit_sub_post s0 s)
      | 0x4d944 | 0x4d946 => Some (isalnum_digit_cmp_post s0 s)
      | 0x4d948 => Some (isalnum_mid s0 s)
      | 0x4d94c => Some (isalnum_early s0 s)
      | 0x4d94a | 0x4d94e => Some (isalnum_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isalnum_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => (a =? isalnum_return) || (a =? isalnum_early_return)
  | _ => false
  end.

Theorem isalnum_nwc : forall s1 s2, isalnum_armv7 s1 = isalnum_armv7 s2.
Proof. reflexivity. Qed.

Theorem isalnum_welltyped : welltyped_prog arm7typctx isalnum_armv7.
Proof. exact welltyped. Qed.

Theorem isalnum_preserves_memory :
  forall_endstates isalnum_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isalnum_preserves_lr :
  forall_endstates isalnum_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isalnum_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isalnum_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isalnum_correct :
  forall prog (EXT : isalnum_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isalnum_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isalnum_invs s0) isalnum_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isalnum_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isalnum_invs.
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
        apply isalnum_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isalnum_orr_post, isalnum_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isalnum_orr_post, isalnum_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold isalnum_sub_post, isalnum_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity;
          rewrite <- ?R3; reflexivity.

      * unfold isalnum_sub_post, isalnum_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold isalnum_cmp_post, isalnum_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec ((s0 R_R0) .| 0x20) 0x61 0x7a) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change ((((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x19) =
                (((s0 R_R0) .| 0x20) mod 2^32 =? 0x7a)) in H.
        rewrite H, <- ?R3. reflexivity.

      * unfold isalnum_cmp_post, isalnum_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy (((s0 R_R0) .| 0x20) ⊖ 0x61) 0x19)
          as [LT|[EQ|GT]].
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = true)
             by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = false)
             by (apply N.leb_gt; exact LT).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. arm7_step.
           unfold isalnum_early, isalnum_test, isalnum_alpha, isalnum_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = true)
             by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = true)
             by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. arm7_step.
           unfold isalnum_early, isalnum_test, isalnum_alpha, isalnum_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = false)
             by (apply N.leb_gt; exact GT).
           assert (HCF : (0x19 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. arm7_step.
           unfold isalnum_digit_entry, isalnum_alpha, isalnum_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isalnum_digit_entry, isalnum_frame in PRE.
        destruct PRE as (R0 & HA & MEM & SP & LR).
        arm7_step.
        unfold isalnum_digit_sub_post, isalnum_frame.
        elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isalnum_digit_sub_post, isalnum_frame in PRE.
        destruct PRE as (R0 & HA & MEM & SP & LR).
        arm7_step.
        unfold isalnum_digit_cmp_post, isalnum_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec (s0 R_R0) 0x30 0x39) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((s0 R_R0) ⊖ 0x30 =? 0x9) = (s0 R_R0 mod 2^32 =? 0x39)) in H.
        rewrite H, <- ?R0. reflexivity.

      * unfold isalnum_digit_cmp_post, isalnum_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
        arm7_step.
        unfold isalnum_digit_cmp_post, isalnum_frame.
        elimstore. repeat split; assumption.

      * unfold isalnum_digit_cmp_post, isalnum_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
        solve_range_movhi ((s0 R_R0) ⊖ 0x30) 0x9 isalnum_mid isalnum_frame.

      * unfold isalnum_mid, isalnum_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
        destruct (N.lt_trichotomy ((s0 R_R0) ⊖ 0x30) 0x9) as [LT|[EQ|GT]].
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
           rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
           rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
           rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isalnum_early, isalnum_frame in PRE.
        destruct PRE as (HT & MEM & SP & LR).
        arm7_step.
        unfold isalnum_post, isalnum_frame. rewrite HT.
        elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
