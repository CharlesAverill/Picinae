(* strlen -- length of a NUL-terminated byte string

   SEMANTICS
   ---------
   The implementation scans unaligned prefixes byte by byte, uses a word-wise
   zero-byte test on aligned words, and finishes with a byte loop.  The proof
   uses one nonzero-prefix invariant at all three loop heads.

   SPECIFICATION (ISO C / POSIX strlen)
   ------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strlen(const char *s);

     DESCRIPTION
            strlen() returns the number of bytes before the first NUL.  As usual
            for partial correctness, invalid or unterminated inputs need not
            reach a return cut.  The postcondition chooses the first NUL index;
            its register representation is modulo 2^32.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            strlen at ELF VA 0x4b963 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5b962.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see strlen_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = s.  Start at 0x5b962.
   Output:  At either BX LR, there is k such that all bytes before k are nonzero,
            the byte at k is zero, and R0 = k mod 2^32.  Memory, SP, LR, and
            callee-saved registers are unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32 armv7_string strlen_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition strlen_entry : addr := 0x5b962.
Definition strlen_return : addr := 0x5b978.
Definition strlen_word_return : addr := 0x5b99e.

Definition strlen_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition strlen_byte_loop (s0 s : store) : Prop :=
  exists k,
    s R_R12 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊕ k /\
    nonzero_prefix (s0 V_MEM32) (s0 R_R0) k /\ strlen_frame s0 s.

Definition strlen_word_loop (s0 s : store) : Prop :=
  exists k,
    s R_R12 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊕ k /\
    nonzero_prefix (s0 V_MEM32) (s0 R_R0) k /\ strlen_frame s0 s.

Definition strlen_final_loop (s0 s : store) : Prop :=
  exists k,
    s R_R12 = s0 R_R0 /\ s R_R2 = (s0 R_R0) ⊕ k /\
    nonzero_prefix (s0 V_MEM32) (s0 R_R0) k /\ strlen_frame s0 s.

Definition strlen_post (s0 s : store) : Prop :=
  exists k,
    s R_R0 = k mod 2^32 /\
    nonzero_prefix (s0 V_MEM32) (s0 R_R0) k /\
    (s0 V_MEM32) Ⓑ[(s0 R_R0) + k] = 0 /\ strlen_frame s0 s.

Definition strlen_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5b962 => Some (s = s0)
      | 0x5b966 => Some (strlen_byte_loop s0 s)
      | 0x5b97a => Some (strlen_word_loop s0 s)
      | 0x5b990 => Some (strlen_final_loop s0 s)
      | 0x5b978 | 0x5b99e => Some (strlen_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition strlen_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => (a =? strlen_return) || (a =? strlen_word_return)
  | _ => false
  end.

Theorem strlen_nwc : forall s1 s2, strlen_armv7 s1 = strlen_armv7 s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped : welltyped_prog arm7typctx strlen_armv7.
Proof. exact welltyped. Qed.

Theorem strlen_preserves_memory :
  forall_endstates strlen_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strlen_preserves_lr :
  forall_endstates strlen_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strlen_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates strlen_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem strlen_correct :
  forall prog (EXT : strlen_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr strlen_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (strlen_invs s0) strlen_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := strlen_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold strlen_invs.
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
        apply strlen_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        do 2 arm7_step. unfold strlen_byte_loop, strlen_frame.
        exists 0. repeat split.
        all: elimstore; psimpl; try assumption; try reflexivity; try lia.
        intros i HI. lia.

      * unfold strlen_byte_loop, strlen_frame in PRE.
        destruct PRE as (k & R12 & R3 & PREFIX & MEM & SP & LR).
        do 2 arm7_step.
        -- unfold strlen_word_loop, strlen_frame. exists k.
           repeat split; elimstore; psimpl; try assumption; try reflexivity.
        -- do 4 arm7_step. arm7_step.
           destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] =? 0) eqn:Z;
             simpl in BC0; try discriminate.
           ++ apply N.eqb_eq in Z. arm7_step.
              unfold strlen_post, strlen_frame. exists k. repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: pose proof (PREFIX i H) as Q; try assumption.
           ++ apply N.eqb_neq in BC0. unfold strlen_byte_loop, strlen_frame.
              exists (k+1). repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: try (pose proof (nonzero_prefix_succ (s0 V_MEM32) (s0 R_R0)
                                k PREFIX BC0 i H) as Q; assumption).
              replace (1+k) with (k+1) by lia.
              apply nonzero_prefix_succ; assumption.

      * unfold strlen_word_loop, strlen_frame in PRE.
        destruct PRE as (k & R12 & R3 & PREFIX & MEM & SP & LR).
        do 7 arm7_step.
        -- unfold strlen_word_loop, strlen_frame. exists (k+4). repeat split.
           all: elimstore; psimpl; try assumption; try reflexivity; try lia.
           destruct (zero32 ((s0 V_MEM32) Ⓓ[(s0 R_R0) + k]) =? 0) eqn:Z;
             simpl in BC; try discriminate.
           apply N.eqb_eq in Z. replace (4+k) with (k+4) by lia.
           apply nonzero_prefix_word; assumption.
           unfold zero32 in Z. rewrite Z in BC; simpl in BC; discriminate.
        -- unfold strlen_final_loop, strlen_frame. exists k. repeat split.
           all: elimstore; psimpl; try assumption; try reflexivity.

      * unfold strlen_final_loop, strlen_frame in PRE.
        destruct PRE as (k & R12 & R2 & PREFIX & MEM & SP & LR).
        do 4 arm7_step. arm7_step.
        destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] =? 0) eqn:Z;
          simpl in BC; try discriminate.
        -- apply N.eqb_eq in Z. arm7_step.
           unfold strlen_post, strlen_frame. exists k. repeat split.
           all: elimstore; psimpl; try assumption; try reflexivity; try lia.
           all: pose proof (PREFIX i H) as Q; try assumption.
        -- apply N.eqb_neq in BC. unfold strlen_final_loop, strlen_frame.
           exists (k+1). repeat split.
           all: elimstore; psimpl; try assumption; try reflexivity; try lia.
           all: try (pose proof (nonzero_prefix_succ (s0 V_MEM32) (s0 R_R0)
                             k PREFIX BC i H) as Q; assumption).
           replace (1+k) with (k+1) by lia.
           apply nonzero_prefix_succ; assumption.
Qed.
