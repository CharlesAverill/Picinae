(* strcmp -- compare two NUL-terminated byte strings

   SEMANTICS
   ---------
   The implementation uses pre-indexed byte loads and advances both pointers
   together.  It stops at unequal bytes or at an equal pair of NUL bytes, then
   returns the modular 32-bit difference of the final pair.

   SPECIFICATION (ISO C / POSIX strcmp)
   ------------------------------------

     SYNOPSIS
            #include <string.h>
            int strcmp(const char *s1, const char *s2);

     DESCRIPTION
            strcmp() compares two null-terminated strings.  The theorem identifies
            the first differing-or-terminating index and gives the exact binary
            result.  As usual for partial correctness, invalid or unterminated
            inputs need not reach a return cut.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            strcmp at ELF VA 0x4b76d (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5b76c.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see strcmp_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = s1, R1 = s2.  Start at 0x5b76c.
   Output:  At BX LR at 0x5b784, there is k such that all earlier bytes are
            equal and nonzero.  Either the bytes at k are both zero and R0 = 0,
            or they differ and R0 = byte1 - byte2 mod 2^32.  Memory, SP, LR,
            and callee-saved registers are unchanged.  The proof stops before
            BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import strcmp_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition strcmp_entry : addr := 0x5b76c.
Definition strcmp_return : addr := 0x5b784.

Definition strcmp_prefix (m : memory) (p1 p2 k : N) : Prop :=
  forall i, i < k -> m Ⓑ[p1+i] = m Ⓑ[p2+i] /\ 0 < m Ⓑ[p1+i].

Lemma strcmp_prefix_succ m p1 p2 k :
  strcmp_prefix m p1 p2 k ->
  m Ⓑ[p1+k] = m Ⓑ[p2+k] -> m Ⓑ[p2+k] <> 0 ->
  strcmp_prefix m p1 p2 (k+1).
Proof.
  intros H E NZ i HI. rewrite N.add_1_r in HI.
  apply N.lt_succ_r, N.le_lteq in HI. destruct HI as [LT|EQ].
  - apply H. exact LT.
  - subst i. split; [exact E|]. rewrite E. apply N.neq_0_lt_0. exact NZ.
Qed.

Definition strcmp_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition strcmp_loop (s0 s : store) : Prop :=
  exists k,
    s R_R2 = ((s0 R_R0) ⊕ k) ⊖ 1 /\
    s R_R1 = ((s0 R_R1) ⊕ k) ⊖ 1 /\
    strcmp_prefix (s0 V_MEM32) (s0 R_R0) (s0 R_R1) k /\
    strcmp_frame s0 s.

Definition strcmp_post (s0 s : store) : Prop :=
  exists k,
    strcmp_prefix (s0 V_MEM32) (s0 R_R0) (s0 R_R1) k /\
    (((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] = 0 /\
      (s0 V_MEM32) Ⓑ[(s0 R_R1) + k] = 0 /\ s R_R0 = 0) \/
     ((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] <>
      (s0 V_MEM32) Ⓑ[(s0 R_R1) + k] /\
      s R_R0 = (s0 V_MEM32) Ⓑ[(s0 R_R0) + k] ⊖
               (s0 V_MEM32) Ⓑ[(s0 R_R1) + k])) /\
    strcmp_frame s0 s.

Definition strcmp_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5b76c => Some (s = s0)
      | 0x5b770 => Some (strcmp_loop s0 s)
      | 0x5b784 => Some (strcmp_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition strcmp_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? strcmp_return
  | _ => false
  end.

Theorem strcmp_nwc : forall s1 s2, strcmp_armv7 s1 = strcmp_armv7 s2.
Proof. reflexivity. Qed.

Theorem strcmp_welltyped : welltyped_prog arm7typctx strcmp_armv7.
Proof. exact welltyped. Qed.

Theorem strcmp_preserves_memory :
  forall_endstates strcmp_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strcmp_preserves_lr :
  forall_endstates strcmp_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strcmp_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates strcmp_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem strcmp_correct :
  forall prog (EXT : strcmp_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr strcmp_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (strcmp_invs s0) strcmp_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := strcmp_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold strcmp_invs.
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
        apply strcmp_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        do 2 arm7_step.
        unfold strcmp_loop, strcmp_frame. exists 0. repeat split.
        all: elimstore; psimpl; try assumption; try reflexivity; try lia.

      * unfold strcmp_loop, strcmp_frame in PRE.
        destruct PRE as (k & R2 & R1 & PREFIX & MEM & SP & LR).
        do 3 arm7_step. arm7_step.
        -- destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] =?
                    (s0 V_MEM32) Ⓑ[(s0 R_R1) + k]) eqn:E;
             simpl in BC.
           ** apply N.eqb_eq in E. do 2 arm7_step.
              destruct ((s0 V_MEM32) Ⓑ[(s0 R_R1) + k] =? 0) eqn:Z;
                simpl in BC0; try discriminate.
              ++ apply N.eqb_eq in Z. do 2 arm7_step.
                 unfold strcmp_post, strcmp_frame. exists k. repeat split.
                 all: elimstore; psimpl; try assumption; try reflexivity; try lia.
                 all: destruct (PREFIX i H) as [Q1 Q2]; try assumption.
              ++ apply N.eqb_neq in BC0. unfold strcmp_loop, strcmp_frame.
                 exists (k+1). repeat split.
                 all: elimstore; psimpl; try assumption; try reflexivity; try lia.
                 all: pose proof (strcmp_prefix_succ (s0 V_MEM32) (s0 R_R0)
                                    (s0 R_R1) k PREFIX E BC0 i H) as Q;
                   destruct Q as [Q1 Q2]; try assumption.
           ** discriminate BC.
        -- destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) + k] =?
                    (s0 V_MEM32) Ⓑ[(s0 R_R1) + k]) eqn:E;
             simpl in BC.
           ** discriminate BC.
           ** apply N.eqb_neq in E. arm7_step.
              unfold strcmp_post, strcmp_frame. exists k. repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: destruct (PREFIX i H) as [Q1 Q2]; try assumption.
Qed.
