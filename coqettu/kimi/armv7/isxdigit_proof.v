(* isxdigit -- test for an ASCII hexadecimal digit

   SEMANTICS
   ---------
   An unsigned range test first recognizes decimal digits and returns one early.
   Other inputs are case-folded with ORR #0x20 and tested for 'a' through 'f'.

   SPECIFICATION (ISO C / POSIX isxdigit)
   --------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int isxdigit(int c);

     DESCRIPTION
            isxdigit() tests whether c is a hexadecimal-digit character.  The
            theorem specifies exact full-register behavior, including modular
            arithmetic.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isxdigit at ELF VA 0x3dbb7 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4dbb6.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isxdigit_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4dbb6.
   Output:  At either BX LR, R0 = 1 when (c - 0x30) mod 2^32 <= 9 or
            ((c OR 0x20) - 0x61) mod 2^32 <= 5, and zero otherwise.  Memory,
            SP, LR, and callee-saved registers are unchanged.  The proof stops
            before the return instruction.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isxdigit_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition isxdigit_entry : addr := 0x4dbb6.
Definition isxdigit_return : addr := 0x4dbcc.
Definition isxdigit_early_return : addr := 0x4dbd0.

Definition isxdigit_digit (x : N) : bool := ((x ⊖ 0x30) <=? 0x9).
Definition isxdigit_alpha (x : N) : bool := (((x .| 0x20) ⊖ 0x61) <=? 0x5).
Definition isxdigit_test (x : N) : bool := isxdigit_digit x || isxdigit_alpha x.

Definition isxdigit_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isxdigit_sub_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x30 /\ isxdigit_frame s0 s.

Definition isxdigit_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x30 /\
  s R_CF = (if 0x9 <=? (s0 R_R0) ⊖ 0x30 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x30 =? 0x9 then 1 else 0) /\
  isxdigit_frame s0 s.

Definition isxdigit_alpha_entry (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  isxdigit_digit (s0 R_R0) = false /\ isxdigit_frame s0 s.

Definition isxdigit_orr_post (s0 s : store) : Prop :=
  s R_R0 = (s0 R_R0) .| 0x20 /\
  isxdigit_digit (s0 R_R0) = false /\ isxdigit_frame s0 s.

Definition isxdigit_alpha_sub_post (s0 s : store) : Prop :=
  s R_R0 = ((s0 R_R0) .| 0x20) ⊖ 0x61 /\
  isxdigit_digit (s0 R_R0) = false /\ isxdigit_frame s0 s.

Definition isxdigit_alpha_cmp_post (s0 s : store) : Prop :=
  s R_R0 = ((s0 R_R0) .| 0x20) ⊖ 0x61 /\
  s R_CF = (if 0x5 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61 then 1 else 0) /\
  s R_ZF = (if ((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5 then 1 else 0) /\
  isxdigit_digit (s0 R_R0) = false /\ isxdigit_frame s0 s.

Definition isxdigit_mid (s0 s : store) : Prop :=
  s R_R0 = (if ((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x5
            then ((s0 R_R0) .| 0x20) ⊖ 0x61 else 0) /\
  s R_CF = (if 0x5 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61 then 1 else 0) /\
  s R_ZF = (if ((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5 then 1 else 0) /\
  isxdigit_digit (s0 R_R0) = false /\ isxdigit_frame s0 s.

Definition isxdigit_early (s0 s : store) : Prop :=
  isxdigit_test (s0 R_R0) = true /\ isxdigit_frame s0 s.

Definition isxdigit_post (s0 s : store) : Prop :=
  s R_R0 = (if isxdigit_test (s0 R_R0) then 1 else 0) /\
  isxdigit_frame s0 s.

Definition isxdigit_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4dbb6 => Some (s = s0)
      | 0x4dbba => Some (isxdigit_sub_post s0 s)
      | 0x4dbbc => Some (isxdigit_cmp_post s0 s)
      | 0x4dbbe => Some (isxdigit_alpha_entry s0 s)
      | 0x4dbc2 => Some (isxdigit_orr_post s0 s)
      | 0x4dbc4 => Some (isxdigit_alpha_sub_post s0 s)
      | 0x4dbc6 | 0x4dbc8 => Some (isxdigit_alpha_cmp_post s0 s)
      | 0x4dbca => Some (isxdigit_mid s0 s)
      | 0x4dbce => Some (isxdigit_early s0 s)
      | 0x4dbcc | 0x4dbd0 => Some (isxdigit_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isxdigit_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => (a =? isxdigit_return) || (a =? isxdigit_early_return)
  | _ => false
  end.

Theorem isxdigit_nwc : forall s1 s2, isxdigit_armv7 s1 = isxdigit_armv7 s2.
Proof. reflexivity. Qed.

Theorem isxdigit_welltyped : welltyped_prog arm7typctx isxdigit_armv7.
Proof. exact welltyped. Qed.

Theorem isxdigit_preserves_memory :
  forall_endstates isxdigit_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isxdigit_preserves_lr :
  forall_endstates isxdigit_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isxdigit_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isxdigit_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isxdigit_correct :
  forall prog (EXT : isxdigit_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isxdigit_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isxdigit_invs s0) isxdigit_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isxdigit_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isxdigit_invs.
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
        apply isxdigit_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isxdigit_sub_post, isxdigit_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isxdigit_sub_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_cmp_post, isxdigit_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec (s0 R_R0) 0x30 0x39) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((s0 R_R0) ⊖ 0x30 =? 0x9) = (s0 R_R0 mod 2^32 =? 0x39)) in H.
        rewrite H, <- ?R3. reflexivity.

      * unfold isxdigit_cmp_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy ((s0 R_R0) ⊖ 0x30) 0x9) as [LT|[EQ|GT]].
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. arm7_step.
           unfold isxdigit_early, isxdigit_test, isxdigit_digit, isxdigit_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. arm7_step.
           unfold isxdigit_early, isxdigit_test, isxdigit_digit, isxdigit_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x30 <=? 0x9) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x9 <=? (s0 R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. arm7_step.
           unfold isxdigit_alpha_entry, isxdigit_digit, isxdigit_frame.
           rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isxdigit_alpha_entry, isxdigit_frame in PRE.
        destruct PRE as (R0 & HD & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_orr_post, isxdigit_frame.
        elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isxdigit_orr_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & HD & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_alpha_sub_post, isxdigit_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity;
          rewrite <- ?R0; reflexivity.

      * unfold isxdigit_alpha_sub_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & HD & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_alpha_cmp_post, isxdigit_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec ((s0 R_R0) .| 0x20) 0x61 0x66) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change ((((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5) =
                (((s0 R_R0) .| 0x20) mod 2^32 =? 0x66)) in H.
        rewrite H, <- ?R0. reflexivity.

      * unfold isxdigit_alpha_cmp_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HD & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_alpha_cmp_post, isxdigit_frame.
        elimstore. repeat split; assumption.

      * unfold isxdigit_alpha_cmp_post, isxdigit_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HD & MEM & SP & LR).
        solve_range_movhi (((s0 R_R0) .| 0x20) ⊖ 0x61) 0x5 isxdigit_mid isxdigit_frame.

      * unfold isxdigit_mid, isxdigit_frame in PRE.
        destruct PRE as (R0 & CF & ZF & HD & MEM & SP & LR).
        destruct (N.lt_trichotomy (((s0 R_R0) .| 0x20) ⊖ 0x61) 0x5)
          as [LT|[EQ|GT]].
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x5) = true)
             by (apply N.leb_le; lia).
           assert (HCF : (0x5 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = false)
             by (apply N.leb_gt; exact LT).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isxdigit_post, isxdigit_test, isxdigit_alpha, isxdigit_frame.
           rewrite HD, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x5) = true)
             by (apply N.leb_le; lia).
           assert (HCF : (0x5 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5) = true)
             by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isxdigit_post, isxdigit_test, isxdigit_alpha, isxdigit_frame.
           rewrite HD, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
        -- assert (HLE : (((s0 R_R0) .| 0x20) ⊖ 0x61 <=? 0x5) = false)
             by (apply N.leb_gt; exact GT).
           assert (HCF : (0x5 <=? ((s0 R_R0) .| 0x20) ⊖ 0x61) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((s0 R_R0) .| 0x20) ⊖ 0x61 =? 0x5) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
           unfold isxdigit_post, isxdigit_test, isxdigit_alpha, isxdigit_frame.
           rewrite HD, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold isxdigit_early, isxdigit_frame in PRE.
        destruct PRE as (HT & MEM & SP & LR).
        arm7_step.
        unfold isxdigit_post, isxdigit_frame. rewrite HT.
        elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
