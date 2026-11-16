(* isprint -- test for an ASCII printing character including space

   SEMANTICS
   ---------
   The function subtracts 0x20 (space) and returns one exactly when the
   modular 32-bit difference is at most 0x5e, selecting ASCII 0x20 through 0x7e.

   SPECIFICATION (ISO C / POSIX isprint)
   ------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int isprint(int c);

     DESCRIPTION
            isprint() tests whether c is a printing character, including space.
            The theorem specifies exact full-register behavior for all inputs.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isprint at ELF VA 0x3d9c7 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d9c6.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isprint_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d9c6.
   Output:  At BX LR at 0x4d9d0, R0 = 1 when (c - 0x20) mod 2^32 <= 0x5e and
            R0 = 0 otherwise.  Memory, SP, LR, and callee-saved registers are
            unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isprint_armv7.
Import ARM7Notations.
Open Scope N.

Definition isprint_entry : addr := 0x4d9c6.
Definition isprint_return : addr := 0x4d9d0.

Definition isprint_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isprint_sub_post (s0 s : store) : Prop :=
  s R_R0 = (s0 R_R0) ⊖ 0x20 /\ isprint_frame s0 s.

Definition isprint_cmp_post (s0 s : store) : Prop :=
  s R_R0 = (s0 R_R0) ⊖ 0x20 /\
  s R_CF = (if 0x5e <=? (s0 R_R0) ⊖ 0x20 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x20 =? 0x5e then 1 else 0) /\
  isprint_frame s0 s.

Definition isprint_mid (s0 s : store) : Prop :=
  s R_R0 = (if (s0 R_R0) ⊖ 0x20 <=? 0x5e then (s0 R_R0) ⊖ 0x20 else 0) /\
  s R_CF = (if 0x5e <=? (s0 R_R0) ⊖ 0x20 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x20 =? 0x5e then 1 else 0) /\
  isprint_frame s0 s.

Definition isprint_post (s0 s : store) : Prop :=
  s R_R0 = (if (s0 R_R0) ⊖ 0x20 <=? 0x5e then 1 else 0) /\
  isprint_frame s0 s.

Definition isprint_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d9c6 => Some (s = s0)
      | 0x4d9c8 => Some (isprint_sub_post s0 s)
      | 0x4d9ca | 0x4d9cc => Some (isprint_cmp_post s0 s)
      | 0x4d9ce => Some (isprint_mid s0 s)
      | 0x4d9d0 => Some (isprint_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isprint_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? isprint_return
  | _ => false
  end.

Theorem isprint_nwc : forall s1 s2, isprint_armv7 s1 = isprint_armv7 s2.
Proof. reflexivity. Qed.

Theorem isprint_welltyped : welltyped_prog arm7typctx isprint_armv7.
Proof. exact welltyped. Qed.

Theorem isprint_preserves_memory :
  forall_endstates isprint_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isprint_preserves_lr :
  forall_endstates isprint_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isprint_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isprint_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isprint_correct :
  forall prog (EXT : isprint_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isprint_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isprint_invs s0) isprint_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isprint_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isprint_invs.
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
        apply isprint_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isprint_sub_post, isprint_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isprint_sub_post, isprint_frame in PRE.
        destruct PRE as (R0 & MEM & SP & LR).
        arm7_step.
        unfold isprint_cmp_post, isprint_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec (s0 R_R0) 0x20 0x7e) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((s0 R_R0) ⊖ 0x20 =? 0x5e) = (s0 R_R0 mod 2^32 =? 0x7e)) in H.
        rewrite H, <- ?R0. reflexivity.

      * unfold isprint_cmp_post, isprint_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold isprint_cmp_post, isprint_frame.
        elimstore. repeat split; assumption.

      * unfold isprint_cmp_post, isprint_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        solve_range_movhi ((s0 R_R0) ⊖ 0x20) 0x5e isprint_mid isprint_frame.

      * unfold isprint_mid, isprint_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy ((s0 R_R0) ⊖ 0x20) 0x5e) as [LT|[EQ|GT]].
        -- assert (HLE : ((s0 R_R0) ⊖ 0x20 <=? 0x5e) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x5e <=? (s0 R_R0) ⊖ 0x20) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : ((s0 R_R0) ⊖ 0x20 =? 0x5e) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isprint_post, isprint_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x20 <=? 0x5e) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x5e <=? (s0 R_R0) ⊖ 0x20) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x20 =? 0x5e) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isprint_post, isprint_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x20 <=? 0x5e) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x5e <=? (s0 R_R0) ⊖ 0x20) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x20 =? 0x5e) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isprint_post, isprint_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
Qed.
