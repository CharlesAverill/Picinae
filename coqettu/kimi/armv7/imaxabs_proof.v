(* imaxabs -- intmax_t signed absolute value

   SEMANTICS
   ---------
   On ARMv7, intmax_t is a 64-bit register pair.  The implementation forms the
   high word's arithmetic sign mask, XORs both words with it, and subtracts the
   mask with borrow.  This is modular 64-bit negation for negative inputs and
   the identity otherwise, including the concrete INTMAX_MIN result.

   SPECIFICATION (ISO C / POSIX imaxabs)
   -------------------------------------

     SYNOPSIS
            #include <inttypes.h>
            intmax_t imaxabs(intmax_t j);

     DESCRIPTION
            imaxabs() computes the absolute value of its argument.  C leaves
            imaxabs(INTMAX_MIN) undefined; this theorem specifies the actual
            binary result as modular 64-bit negation.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            imaxabs at ELF VA 0x4a5cd (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5a5cc.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see imaxabs_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = low word of j, R1 = high word.  Start at 0x5a5cc.
   Output:  At BX LR at 0x5a5dc, R0/R1 contain the low/high words of the
            absolute-value bit pattern.  For a negative high word, R0 = -R0
            mod 2^32 and R1 = -R1 - borrow mod 2^32, where borrow is zero
            exactly when the input low word is zero.  Otherwise R0 and R1 are
            unchanged.  Memory, SP, LR, and callee-saved registers are
            unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_abs64 imaxabs_armv7.
Import ARM7Notations.
Open Scope N.

Definition imaxabs_entry : addr := 0x5a5cc.
Definition imaxabs_return : addr := 0x5a5dc.

Definition imaxabs_frame (s0 s : store) : Prop :=
  s0 R_R0 < 2^32 /\ s0 R_R1 < 2^32 /\
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition imaxabs_asr_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R1 = s0 R_R1 /\
  s R_R3 = signmask32 (s0 R_R1) /\ imaxabs_frame s0 s.

Definition imaxabs_xor_low_post (s0 s : store) : Prop :=
  s R_R0 = N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) /\
  s R_R1 = s0 R_R1 /\ s R_R3 = signmask32 (s0 R_R1) /\
  imaxabs_frame s0 s.

Definition imaxabs_sub_low_post (s0 s : store) : Prop :=
  s R_R0 = (N.lxor (s0 R_R0) (signmask32 (s0 R_R1))) ⊖ (signmask32 (s0 R_R1)) /\
  s R_R1 = s0 R_R1 /\ s R_R3 = signmask32 (s0 R_R1) /\
  s R_CF = (if signmask32 (s0 R_R1) <=?
              N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) then 1 else 0) /\
  imaxabs_frame s0 s.

Definition imaxabs_xor_high_post (s0 s : store) : Prop :=
  s R_R0 = (N.lxor (s0 R_R0) (signmask32 (s0 R_R1))) ⊖ (signmask32 (s0 R_R1)) /\
  s R_R1 = N.lxor (s0 R_R1) (signmask32 (s0 R_R1)) /\
  s R_R3 = signmask32 (s0 R_R1) /\
  s R_CF = (if signmask32 (s0 R_R1) <=?
              N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) then 1 else 0) /\
  imaxabs_frame s0 s.

Definition imaxabs_post (s0 s : store) : Prop :=
  s R_R0 = abs64_low (s0 R_R1) (s0 R_R0) /\
  s R_R1 = abs64_high (s0 R_R1) (s0 R_R0) /\
  imaxabs_frame s0 s.

Definition imaxabs_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5a5cc => Some (s = s0)
      | 0x5a5ce => Some (imaxabs_asr_post s0 s)
      | 0x5a5d2 => Some (imaxabs_xor_low_post s0 s)
      | 0x5a5d4 => Some (imaxabs_sub_low_post s0 s)
      | 0x5a5d8 => Some (imaxabs_xor_high_post s0 s)
      | 0x5a5dc => Some (imaxabs_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition imaxabs_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? imaxabs_return
  | _ => false
  end.

Theorem imaxabs_nwc : forall s1 s2, imaxabs_armv7 s1 = imaxabs_armv7 s2.
Proof. reflexivity. Qed.

Theorem imaxabs_welltyped : welltyped_prog arm7typctx imaxabs_armv7.
Proof. exact welltyped. Qed.

Theorem imaxabs_preserves_memory :
  forall_endstates imaxabs_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem imaxabs_preserves_lr :
  forall_endstates imaxabs_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem imaxabs_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates imaxabs_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem imaxabs_correct :
  forall prog (EXT : imaxabs_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr imaxabs_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (imaxabs_invs s0) imaxabs_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := imaxabs_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold imaxabs_invs.
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
        apply imaxabs_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold imaxabs_asr_post, imaxabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold imaxabs_asr_post, imaxabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold imaxabs_xor_low_post, imaxabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold imaxabs_xor_low_post, imaxabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold imaxabs_sub_low_post, imaxabs_frame.
        elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold imaxabs_sub_low_post, imaxabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & CF & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold imaxabs_xor_high_post, imaxabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold imaxabs_xor_high_post, imaxabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & CF & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold imaxabs_post, imaxabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        -- rewrite abs64_low_mask by assumption. reflexivity.
        -- rewrite abs64_high_mask by assumption. reflexivity.
Qed.
