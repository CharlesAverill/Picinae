(* isascii -- test whether an integer fits in 7-bit ASCII

   SEMANTICS
   ---------
   CMP computes the unsigned comparison against 0x7f.  The ITE block returns
   zero for a value above 0x7f and one otherwise.

   SPECIFICATION (POSIX isascii)
   ----------------------------

     SYNOPSIS
            #include <ctype.h>
            int isascii(int c);

     DESCRIPTION
            isascii() tests whether c is a 7-bit US-ASCII character value.

     RETURN VALUE
            isascii() returns nonzero if c is between 0 and 127, and zero
            otherwise.  This proof uses the full 32-bit R0 value, so values
            with any high bit set return zero.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            isascii at ELF VA 0x3d969 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d968.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see isascii_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  The proof starts at 0x4d968.
   Output:  At BX LR at 0x4d970, R0 = 1 when c <= 0x7f and 0 otherwise.
            Memory, SP, LR, and all AAPCS callee-saved registers are unchanged.
            Stopping before BX LR excludes the unmodeled mode-switch userop.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import isascii_armv7.
Import ARM7Notations.
Open Scope N.

Definition isascii_entry : addr := 0x4d968.
Definition isascii_return : addr := 0x4d970.

Definition isascii_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition isascii_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_CF = (if 0x7f <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if s0 R_R0 =? 0x7f then 1 else 0) /\
  isascii_frame s0 s.

Definition isascii_mid (s0 s : store) : Prop :=
  s R_R0 = (if s0 R_R0 <=? 0x7f then s0 R_R0 else 0) /\
  s R_CF = (if 0x7f <=? s0 R_R0 then 1 else 0) /\
  s R_ZF = (if s0 R_R0 =? 0x7f then 1 else 0) /\
  isascii_frame s0 s.

Definition isascii_post (s0 s : store) : Prop :=
  s R_R0 = (if s0 R_R0 <=? 0x7f then 1 else 0) /\
  isascii_frame s0 s.

Definition isascii_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4d968 => Some (s = s0)
      | 0x4d96a | 0x4d96c => Some (isascii_cmp_post s0 s)
      | 0x4d96e => Some (isascii_mid s0 s)
      | 0x4d970 => Some (isascii_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition isascii_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? isascii_return
  | _ => false
  end.

Theorem isascii_nwc : forall s1 s2, isascii_armv7 s1 = isascii_armv7 s2.
Proof. reflexivity. Qed.

Theorem isascii_welltyped : welltyped_prog arm7typctx isascii_armv7.
Proof. exact welltyped. Qed.

Theorem isascii_preserves_memory :
  forall_endstates isascii_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isascii_preserves_lr :
  forall_endstates isascii_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem isascii_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates isascii_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem isascii_correct :
  forall prog (EXT : isascii_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr isascii_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (isascii_invs s0) isascii_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := isascii_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold isascii_invs.
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
        apply isascii_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold isascii_cmp_post, isascii_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold isascii_cmp_post, isascii_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold isascii_cmp_post, isascii_frame.
        elimstore. repeat split; assumption.

      * unfold isascii_cmp_post, isascii_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy (s0 R_R0) 0x7f) as [LT|[EQ|GT]].
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x7f <=? s0 R_R0) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : (s0 R_R0 =? 0x7f) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold isascii_mid, isascii_frame. rewrite HLE, HCF, HZF.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x7f <=? s0 R_R0) = true) by (apply N.leb_le; lia).
           assert (HZF : (s0 R_R0 =? 0x7f) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold isascii_mid, isascii_frame. rewrite HLE, HCF, HZF.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x7f <=? s0 R_R0) = true) by (apply N.leb_le; lia).
           assert (HZF : (s0 R_R0 =? 0x7f) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold isascii_mid, isascii_frame. rewrite HLE, HCF, HZF.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.

      * unfold isascii_mid, isascii_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy (s0 R_R0) 0x7f) as [LT|[EQ|GT]].
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x7f <=? s0 R_R0) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : (s0 R_R0 =? 0x7f) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isascii_post, isascii_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x7f <=? s0 R_R0) = true) by (apply N.leb_le; lia).
           assert (HZF : (s0 R_R0 =? 0x7f) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isascii_post, isascii_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : (s0 R_R0 <=? 0x7f) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x7f <=? s0 R_R0) = true) by (apply N.leb_le; lia).
           assert (HZF : (s0 R_R0 =? 0x7f) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. rewrite HLE in R0.
           arm7_step.
           unfold isascii_post, isascii_frame. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
Qed.
