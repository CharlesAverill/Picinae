(* labs -- 32-bit long-integer absolute value

   SEMANTICS
   ---------
   On ARMv7, long is 32 bits.  CMP sets the signed flags for R0 and the IT
   block negates negative inputs modulo 2^32, including LONG_MIN.

   SPECIFICATION (ISO C / POSIX labs)
   ---------------------------------

     SYNOPSIS
            #include <stdlib.h>
            long labs(long j);

     DESCRIPTION
            labs() computes the absolute value of its long-integer argument.
            C leaves labs(LONG_MIN) undefined; this theorem specifies the actual
            binary result as modular 32-bit negation.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            labs at ELF VA 0x4a603 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5a602.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see labs_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = j.  Start at 0x5a602.
   Output:  At BX LR at 0x5a608, R0 = j when signed-nonnegative and -j mod
            2^32 when signed-negative.  Memory, SP, LR, and all AAPCS
            callee-saved registers are unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import labs_armv7.
Import ARM7Notations.
Open Scope N.

Definition labs_entry : addr := 0x5a602.
Definition labs_return : addr := 0x5a608.

Definition labs32 (x : N) : N := if slt 32 x 0 then 0 ⊖ x else x.

Definition labs_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition labs_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\
  s R_NF = (if slt 32 (s0 R_R0) 0 then 1 else 0) /\
  s R_VF = 0 /\
  labs_frame s0 s.

Definition labs_post (s0 s : store) : Prop :=
  s R_R0 = labs32 (s0 R_R0) /\ labs_frame s0 s.

Definition labs_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5a602 => Some (s = s0)
      | 0x5a604 | 0x5a606 => Some (labs_cmp_post s0 s)
      | 0x5a608 => Some (labs_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition labs_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? labs_return
  | _ => false
  end.

Theorem labs_nwc : forall s1 s2, labs_armv7 s1 = labs_armv7 s2.
Proof. reflexivity. Qed.

Theorem labs_welltyped : welltyped_prog arm7typctx labs_armv7.
Proof. exact welltyped. Qed.

Theorem labs_preserves_memory :
  forall_endstates labs_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem labs_preserves_lr :
  forall_endstates labs_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem labs_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates labs_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem labs_correct :
  forall prog (EXT : labs_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr labs_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (labs_invs s0) labs_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := labs_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold labs_invs.
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
        apply labs_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        arm7_step.
        unfold labs_cmp_post, labs_frame.
        elimstore. repeat split; psimpl;
          rewrite ?msub_0_r, ?N.mod_small by assumption; reflexivity.

      * unfold labs_cmp_post, labs_frame in PRE.
        destruct PRE as (R0 & NF & VF & MEM & SP & LR).
        arm7_step.
        unfold labs_cmp_post, labs_frame.
        elimstore. repeat split; assumption.

      * unfold labs_cmp_post, labs_frame in PRE.
        destruct PRE as (R0 & NF & VF & MEM & SP & LR).
        destruct (slt 32 (s0 R_R0) 0) eqn:NEG.
        -- arm7_step.
           unfold labs_post, labs_frame, labs32. rewrite NEG.
           elimstore. repeat split; psimpl; try assumption; try reflexivity.
        -- arm7_step.
           unfold labs_post, labs_frame, labs32. rewrite NEG.
           elimstore. repeat split; psimpl; try assumption; try reflexivity.
Qed.
