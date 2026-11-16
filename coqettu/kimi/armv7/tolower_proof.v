(* tolower -- ASCII uppercase-to-lowercase conversion

   SEMANTICS
   ---------
   The function tests whether (c - 'A') mod 2^32 is at most 25 and, if so,
   sets bit 5.  All other inputs are returned unchanged.

   SPECIFICATION (ISO C / POSIX tolower)
   ------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int tolower(int c);

     DESCRIPTION
            tolower() converts an uppercase letter to its lowercase equivalent.
            The theorem specifies the exact full-register binary behavior,
            including inputs outside the unsigned-char range.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            tolower at ELF VA 0x3dbdd (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4dbdc.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see tolower_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4dbdc.
   Output:  At BX LR at 0x4dbe8, R0 = c OR 0x20 when
            (c - 0x41) mod 2^32 <= 25, and R0 = c otherwise.  Memory, SP, LR,
            and all AAPCS callee-saved registers are unchanged.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common tolower_armv7.
Import ARM7Notations.
Open Scope N.

Definition tolower_entry : addr := 0x4dbdc.
Definition tolower_return : addr := 0x4dbe8.

Definition tolower32 (x : N) : N :=
  if (x ⊖ 0x41) <=? 0x19 then x .| 0x20 else x.

Definition tolower_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition tolower_sub_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x41 /\ tolower_frame s0 s.

Definition tolower_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x41 /\
  s R_CF = (if 0x19 <=? (s0 R_R0) ⊖ 0x41 then 1 else 0) /\
  s R_ZF = (if (s0 R_R0) ⊖ 0x41 =? 0x19 then 1 else 0) /\
  tolower_frame s0 s.

Definition tolower_post (s0 s : store) : Prop :=
  s R_R0 = tolower32 (s0 R_R0) /\ tolower_frame s0 s.

Definition tolower_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x4dbdc => Some (s = s0)
      | 0x4dbe0 => Some (tolower_sub_post s0 s)
      | 0x4dbe2 | 0x4dbe4 => Some (tolower_cmp_post s0 s)
      | 0x4dbe8 => Some (tolower_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition tolower_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? tolower_return
  | _ => false
  end.

Theorem tolower_nwc : forall s1 s2, tolower_armv7 s1 = tolower_armv7 s2.
Proof. reflexivity. Qed.

Theorem tolower_welltyped : welltyped_prog arm7typctx tolower_armv7.
Proof. exact welltyped. Qed.

Theorem tolower_preserves_memory :
  forall_endstates tolower_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem tolower_preserves_lr :
  forall_endstates tolower_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem tolower_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates tolower_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem tolower_correct :
  forall prog (EXT : tolower_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr tolower_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (tolower_invs s0) tolower_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := tolower_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold tolower_invs.
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
        apply tolower_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold tolower_sub_post, tolower_frame.
        elimstore. repeat split; psimpl; reflexivity.

      * unfold tolower_sub_post, tolower_frame in PRE.
        destruct PRE as (R0 & R3 & MEM & SP & LR).
        arm7_step.
        unfold tolower_cmp_post, tolower_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        pose proof (msub_eqb_spec (s0 R_R0) 0x41 0x5a) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((s0 R_R0) ⊖ 0x41 =? 0x19) = (s0 R_R0 mod 2^32 =? 0x5a)) in H.
        rewrite H, <- ?R3. reflexivity.

      * unfold tolower_cmp_post, tolower_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        arm7_step.
        unfold tolower_cmp_post, tolower_frame.
        elimstore. repeat split; assumption.

      * unfold tolower_cmp_post, tolower_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
        destruct (N.lt_trichotomy ((s0 R_R0) ⊖ 0x41) 0x19) as [LT|[EQ|GT]].
        -- assert (HLE : ((s0 R_R0) ⊖ 0x41 <=? 0x19) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x41) = false) by (apply N.leb_gt; exact LT).
           assert (HZF : ((s0 R_R0) ⊖ 0x41 =? 0x19) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold tolower_post, tolower_frame, tolower32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x41 <=? 0x19) = true) by (apply N.leb_le; lia).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x41) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x41 =? 0x19) = true) by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold tolower_post, tolower_frame, tolower32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
        -- assert (HLE : ((s0 R_R0) ⊖ 0x41 <=? 0x19) = false) by (apply N.leb_gt; exact GT).
           assert (HCF : (0x19 <=? (s0 R_R0) ⊖ 0x41) = true) by (apply N.leb_le; lia).
           assert (HZF : ((s0 R_R0) ⊖ 0x41 =? 0x19) = false) by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *.
           arm7_step.
           unfold tolower_post, tolower_frame, tolower32. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; try reflexivity; try lia.
Qed.
