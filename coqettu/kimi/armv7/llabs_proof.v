(* llabs -- 64-bit signed absolute value

   SEMANTICS
   ---------
   AAPCS passes the low word in R0 and the high word in R1.  The implementation
   forms the high word's arithmetic sign mask in R3, XORs both input words with
   that mask, and subtracts the mask with borrow.  This is modular 64-bit
   negation for negative inputs and the identity otherwise, including the
   concrete LLONG_MIN result.

   SPECIFICATION (ISO C / POSIX llabs)
   -----------------------------------

     SYNOPSIS
            #include <stdlib.h>
            long long llabs(long long j);

     DESCRIPTION
            llabs() computes the absolute value of its argument.  C leaves
            llabs(LLONG_MIN) undefined; this theorem specifies the actual binary
            result as modular 64-bit negation.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            llabs at ELF VA 0x4a61f (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5a61e.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see llabs_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = low word of j, R1 = high word.  Start at 0x5a61e.
   Output:  At BX LR at 0x5a62e, R0/R1 contain the low/high words of the
            absolute-value bit pattern.  For a negative high word, R0 = -R0
            mod 2^32 and R1 = -R1 - borrow mod 2^32, where borrow is zero
            exactly when the input low word is zero.  Otherwise R0 and R1 are
            unchanged.  Memory, SP, LR, and callee-saved registers are
            unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_abs64 llabs_armv7.
Import ARM7Notations.
Open Scope N.

Definition llabs_entry : addr := 0x5a61e.
Definition llabs_return : addr := 0x5a62e.

Definition llabs_frame (s0 s : store) : Prop :=
  s0 R_R0 < 2^32 /\ s0 R_R1 < 2^32 /\
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition llabs_asr_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R1 = s0 R_R1 /\
  s R_R3 = signmask32 (s0 R_R1) /\ llabs_frame s0 s.

Definition llabs_xor_low_post (s0 s : store) : Prop :=
  s R_R0 = N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) /\
  s R_R1 = s0 R_R1 /\ s R_R3 = signmask32 (s0 R_R1) /\
  llabs_frame s0 s.

Definition llabs_sub_low_post (s0 s : store) : Prop :=
  s R_R0 = (N.lxor (s0 R_R0) (signmask32 (s0 R_R1))) ⊖ (signmask32 (s0 R_R1)) /\
  s R_R1 = s0 R_R1 /\ s R_R3 = signmask32 (s0 R_R1) /\
  s R_CF = (if signmask32 (s0 R_R1) <=?
              N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) then 1 else 0) /\
  llabs_frame s0 s.

Definition llabs_xor_high_post (s0 s : store) : Prop :=
  s R_R0 = (N.lxor (s0 R_R0) (signmask32 (s0 R_R1))) ⊖ (signmask32 (s0 R_R1)) /\
  s R_R1 = N.lxor (s0 R_R1) (signmask32 (s0 R_R1)) /\
  s R_R3 = signmask32 (s0 R_R1) /\
  s R_CF = (if signmask32 (s0 R_R1) <=?
              N.lxor (s0 R_R0) (signmask32 (s0 R_R1)) then 1 else 0) /\
  llabs_frame s0 s.

Definition llabs_post (s0 s : store) : Prop :=
  s R_R0 = abs64_low (s0 R_R1) (s0 R_R0) /\
  s R_R1 = abs64_high (s0 R_R1) (s0 R_R0) /\
  llabs_frame s0 s.

Definition llabs_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5a61e => Some (s = s0)
      | 0x5a620 => Some (llabs_asr_post s0 s)
      | 0x5a624 => Some (llabs_xor_low_post s0 s)
      | 0x5a626 => Some (llabs_sub_low_post s0 s)
      | 0x5a62a => Some (llabs_xor_high_post s0 s)
      | 0x5a62e => Some (llabs_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition llabs_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? llabs_return
  | _ => false
  end.

Theorem llabs_nwc : forall s1 s2, llabs_armv7 s1 = llabs_armv7 s2.
Proof. reflexivity. Qed.

Theorem llabs_welltyped : welltyped_prog arm7typctx llabs_armv7.
Proof. exact welltyped. Qed.

Theorem llabs_preserves_memory :
  forall_endstates llabs_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem llabs_preserves_lr :
  forall_endstates llabs_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem llabs_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates llabs_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem llabs_correct :
  forall prog (EXT : llabs_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr llabs_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (llabs_invs s0) llabs_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := llabs_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold llabs_invs.
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
        apply llabs_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold llabs_asr_post, llabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold llabs_asr_post, llabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold llabs_xor_low_post, llabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold llabs_xor_low_post, llabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold llabs_sub_low_post, llabs_frame.
        elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold llabs_sub_low_post, llabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & CF & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold llabs_xor_high_post, llabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        rewrite ashiftr31_signmask. reflexivity.

      * unfold llabs_xor_high_post, llabs_frame in PRE.
        destruct PRE as (R0 & R1 & R3 & CF & HLO & HHI & MEM & SP & LR).
        arm7_step.
        unfold llabs_post, llabs_frame.
        elimstore. repeat split; psimpl; try assumption; try reflexivity.
        -- rewrite abs64_low_mask by assumption. reflexivity.
        -- rewrite abs64_high_mask by assumption. reflexivity.
Qed.
