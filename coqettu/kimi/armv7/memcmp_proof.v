(* memcmp -- compare two byte arrays

   SEMANTICS
   ---------
   The implementation is a byte-at-a-time loop.  R0/R1 advance together and R2
   counts down.  It returns zero after n equal bytes, or the modular 32-bit
   difference between the first unequal pair of bytes.

   SPECIFICATION (ISO C / POSIX memcmp)
   ------------------------------------

     SYNOPSIS
            #include <string.h>
            int memcmp(const void *s1, const void *s2, size_t n);

     DESCRIPTION
            memcmp() compares the first n bytes of s1 and s2.  The result is zero
            when all n bytes match; otherwise its sign follows the first unequal
            pair interpreted as unsigned bytes.  The theorem gives the exact
            difference produced by this binary.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            memcmp at ELF VA 0x4b0b3 (Thumb); Ghidra image base 0x10000,
            lifted entry and loop head 0x5b0b2.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see memcmp_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = s1, R1 = s2, R2 = n.  Start at 0x5b0b2.
   Output:  At either BX LR, there is k <= n such that all bytes before k match.
            If k = n then R0 = 0.  Otherwise k < n, the bytes at k differ, and
            R0 = byte1 - byte2 mod 2^32.  Memory, SP, LR, and callee-saved
            registers are unchanged.  The proof stops before BX LR.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import memcmp_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition memcmp_entry : addr := 0x5b0b2.
Definition memcmp_return : addr := 0x5b0cc.
Definition memcmp_zero_return : addr := 0x5b0d0.

Definition memcmp_prefix (m : memory) (p1 p2 k : N) : Prop :=
  forall i, i < k -> m Ⓑ[p1 ⊕ i] = m Ⓑ[p2 ⊕ i].

Lemma memcmp_prefix_succ m p1 p2 k :
  memcmp_prefix m p1 p2 k ->
  m Ⓑ[p1 ⊕ k] = m Ⓑ[p2 ⊕ k] ->
  memcmp_prefix m p1 p2 (k+1).
Proof.
  intros H H0 i HI. rewrite N.add_1_r in HI.
  apply N.lt_succ_r, N.le_lteq in HI. destruct HI as [LT|EQ].
  - apply H. exact LT.
  - subst i. exact H0.
Qed.

Definition memcmp_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\ s R_LR = s0 R_LR.

Definition memcmp_loop (s0 s : store) : Prop :=
  exists k,
    k <= s0 R_R2 /\
    s R_R0 = (s0 R_R0) ⊕ k /\
    s R_R1 = (s0 R_R1) ⊕ k /\
    s R_R2 = (s0 R_R2) ⊖ k /\
    memcmp_prefix (s0 V_MEM32) (s0 R_R0) (s0 R_R1) k /\
    s0 R_R2 < 2^32 /\ memcmp_frame s0 s.

Definition memcmp_post (s0 s : store) : Prop :=
  exists k,
    k <= s0 R_R2 /\
    memcmp_prefix (s0 V_MEM32) (s0 R_R0) (s0 R_R1) k /\
    ((k = s0 R_R2 /\ s R_R0 = 0) \/
     (k < s0 R_R2 /\
      s R_R0 = (s0 V_MEM32) Ⓑ[(s0 R_R0) ⊕ k] ⊖
               (s0 V_MEM32) Ⓑ[(s0 R_R1) ⊕ k] /\
      (s0 V_MEM32) Ⓑ[(s0 R_R0) ⊕ k] <>
      (s0 V_MEM32) Ⓑ[(s0 R_R1) ⊕ k])) /\
    memcmp_frame s0 s.

Definition memcmp_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5b0b2 => Some (memcmp_loop s0 s)
      | 0x5b0cc | 0x5b0d0 => Some (memcmp_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition memcmp_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => (a =? memcmp_return) || (a =? memcmp_zero_return)
  | _ => false
  end.

Theorem memcmp_nwc : forall s1 s2, memcmp_armv7 s1 = memcmp_armv7 s2.
Proof. reflexivity. Qed.

Theorem memcmp_welltyped : welltyped_prog arm7typctx memcmp_armv7.
Proof. exact welltyped. Qed.

Theorem memcmp_preserves_memory :
  forall_endstates memcmp_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem memcmp_preserves_lr :
  forall_endstates memcmp_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem memcmp_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates memcmp_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem memcmp_correct :
  forall prog (EXT : memcmp_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr memcmp_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (memcmp_invs s0) memcmp_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := memcmp_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold memcmp_invs.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - s0 MDL START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step.
      assert (P0 := models_var R_R0 MDL). assert (P1 := models_var R_R1 MDL).
      assert (P2 := models_var R_R2 MDL). unfold arm7typctx in P0, P1, P2.
      unfold memcmp_loop, memcmp_frame. exists 0.
      repeat split; psimpl; try assumption; try reflexivity.
      all: try lia. intros i HI. lia.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply memcmp_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * unfold memcmp_loop, memcmp_frame in PRE.
        destruct PRE as (k & KN & R0 & R1 & R2 & PREFIX & NB & MEM & SP & LR).
        arm7_step.
        -- apply N.eqb_eq in BC.
           rewrite !N.mod_small in BC by lia. subst k.
           arm7_step. unfold memcmp_post, memcmp_frame.
           exists (s0 R_R2). elimstore.
           repeat split; psimpl; try assumption; try lia.
        -- apply N.eqb_neq in BC.
           assert (HK : k < s0 R_R2).
           { destruct (proj1 (N.le_lteq k (s0 R_R2)) KN) as [LT|EQ]; [exact LT|].
             subst k. rewrite !N.mod_small in BC by assumption. contradiction. }
           do 6 arm7_step. arm7_step.
           ++ destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) ⊕ k] =?
                        (s0 V_MEM32) Ⓑ[(s0 R_R1) ⊕ k]) eqn:E;
                simpl in BC0; try discriminate.
              apply N.eqb_eq in E. unfold memcmp_loop, memcmp_frame.
              exists (k+1). repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              replace (1+k) with (k+1) by lia.
              apply memcmp_prefix_succ; assumption.
              unfold memcmp_loop, memcmp_frame. exists (k+1).
              repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                                ((s0 R_R0) + k)) as G1;
                pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                              ((s0 R_R1) + k)) as G2;
                rewrite G1, G2 in E; rewrite E in BC0;
                simpl in BC0; discriminate.
           ++ destruct ((s0 V_MEM32) Ⓑ[(s0 R_R0) ⊕ k] =?
                        (s0 V_MEM32) Ⓑ[(s0 R_R1) ⊕ k]) eqn:E;
                simpl in BC0.
              ** pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                              ((s0 R_R0) + k)) as G1.
                 pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                              ((s0 R_R1) + k)) as G2.
                 rewrite G1, G2 in E. rewrite E in BC0. discriminate.
              ** apply N.eqb_neq in E. arm7_step.
                 unfold memcmp_post, memcmp_frame. exists k.
                 repeat split.
                 all: elimstore; psimpl; try assumption; try reflexivity; try lia.
                 right. repeat split; psimpl; try assumption; try reflexivity; try lia.
                 pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                              ((s0 R_R0) + k)) as G1.
                 pose proof (getmem_mod_l 32 LittleE 1 (s0 V_MEM32)
                              ((s0 R_R1) + k)) as G2.
                 rewrite G1, G2 in E. exact E.
Qed.
