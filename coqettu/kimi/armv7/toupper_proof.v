(* toupper -- ASCII lowercase-to-uppercase conversion

   SEMANTICS
   ---------
   The function tests whether (c - 'a') mod 2^32 is at most 25 and, if so,
   clears bit 5.  All other inputs are returned unchanged.

   SPECIFICATION (ISO C / POSIX toupper)
   ------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int toupper(int c);

     DESCRIPTION
            toupper() converts a lowercase letter to its uppercase equivalent.
            The theorem specifies the exact full-register binary behavior,
            including inputs outside the unsigned-char range.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            toupper at ELF VA 0x3dbef (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4dbee.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see toupper_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4dbee.
   Output:  At BX LR at 0x4dbfa, R0 = c AND 0x5f when
            (c - 0x61) mod 2^32 <= 25, and R0 = c otherwise.  Memory, SP, LR,
            and all AAPCS callee-saved registers are unchanged.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common toupper_armv7.
Import ARM7Notations.
Open Scope N.

Definition toupper_entry : addr := 0x4dbee.
Definition toupper_return : addr := 0x4dbfa.

Definition toupper32 (x : N) : N :=
  if (x ⊖ 0x61) <=? 0x19 then x .& 0x5f else x.

Definition toupper_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition toupper_sub_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x61 /\ toupper_frame s0 s.

Definition toupper_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x61 /\
  s R_CF = (if 0x19 <=? (s0 R_R0) ⊖ 0x61 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x61 =? 0x19 then 1 else 0) /\
  toupper_frame s0 s.

Definition toupper_post (s0 s : store) : Prop :=
  s R_R0 = toupper32 (s0 R_R0) /\ toupper_frame s0 s.

Definition toupper_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4dbee => Some (s = s0)
      | 0x4dbf2 => Some (toupper_sub_post s0 s)
      | 0x4dbf4 | 0x4dbf6 => Some (toupper_cmp_post s0 s)
      | 0x4dbfa => Some (toupper_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition toupper_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? toupper_return
  | _ => false
  end.

Theorem toupper_nwc : forall s1 s2, toupper_armv7 s1 = toupper_armv7 s2.
Proof. reflexivity. Qed.

Theorem toupper_welltyped : welltyped_prog arm7typctx toupper_armv7.
Proof. exact welltyped. Qed.

Theorem toupper_preserves_memory :
  forall_endstates toupper_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem toupper_preserves_lr :
  forall_endstates toupper_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem toupper_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates toupper_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem toupper_correct :
  forall prog (EXT : toupper_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr toupper_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (toupper_invs s0) toupper_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := toupper_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold toupper_invs.
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
        apply toupper_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold toupper_sub_post, toupper_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold toupper_sub_post, toupper_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold toupper_cmp_post, toupper_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec (s0 R_R0) 0x61 0x7a) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((s0 R_R0) ⊖ 0x61 =? 0x19) = (s0 R_R0 mod 2^32 =? 0x7a)) in H.
        rewrite H, <- ?R3. reflexivity.

      * unfold toupper_cmp_post, toupper_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold toupper_cmp_post, toupper_frame.
        elimstore. repeat split; assumption.

      * unfold toupper_cmp_post, toupper_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy ((s0 R_R0) ⊖ 0x61) 0x19) as [LT|[EQ|GT]].
        -- assert (HLE : ((s0 R_R0) ⊖ 0x61 <=? 0x19) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x61) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : ((s0 R_R0) ⊖ 0x61 =? 0x19) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold toupper_post, toupper_frame, toupper32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x61 <=? 0x19) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x61) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x61 =? 0x19) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold toupper_post, toupper_frame, toupper32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x61 <=? 0x19) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x61) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x61 =? 0x19) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold toupper_post, toupper_frame, toupper32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
Qed.
