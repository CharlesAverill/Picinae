From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32 armv7_string armv7_memchr memchr_armv7 memchr_proof strnlen_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition strnlen_program : program := updateall2 strnlen_armv7 memchr_armv7.

Lemma strnlen_program_contains_strnlen : strnlen_armv7 ⊆2 strnlen_program.
Proof.
  intros s a insn H. unfold strnlen_program, updateall2, updateall, memchr_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma strnlen_program_contains_memchr : memchr_armv7 ⊆2 strnlen_program.
Proof. apply subset_updateall2. Qed.

Theorem strnlen_program_welltyped : welltyped_prog arm7typctx strnlen_program.
Proof.
  intros s a. unfold strnlen_program, updateall2, updateall.
  destruct (memchr_armv7 s a) as [[sz q]|] eqn:H.
  - pose proof (memchr_armv7.welltyped s a) as WT. rewrite H in WT. exact WT.
  - apply strnlen_armv7.welltyped.
Qed.

Definition strnlen_premem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
      ((s0 R_SP) ⊖ 8) (s0 R_R4))
    ((s0 R_SP) ⊖ 12) (s0 R_R1).

Definition strnlen_finalmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4
        (setmem 32 LittleE 4
          (setmem 32 LittleE 4
            (setmem 32 LittleE 4
              (setmem 32 LittleE 4
                (setmem 32 LittleE 4 (s0 V_MEM32)
                  ((s0 R_SP) ⊖ 4) (s0 R_LR))
                ((s0 R_SP) ⊖ 8) (s0 R_R4))
              ((s0 R_SP) ⊖ 12) (s0 R_R1))
            ((s0 R_SP) ⊖ 20) 0x5bab5)
          ((s0 R_SP) ⊖ 24) (s0 R_R7))
        ((s0 R_SP) ⊖ 28) (s0 R_R6))
      ((s0 R_SP) ⊖ 32) (s0 R_R5))
    ((s0 R_SP) ⊖ 36) (s0 R_R0).

Definition strnlen_precall (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R1 = 0 /\ s R_R2 = s0 R_R2 /\
  s R_R4 = s0 R_R0 /\ s R_R5 = s0 R_R5 /\ s R_R6 = s0 R_R6 /\
  s R_R7 = s0 R_R7 /\ s R_SP = (s0 R_SP) ⊖ 16 /\
  s V_MEM32 = strnlen_premem s0 /\ s R_LR = 0x5bab5.

Definition strnlen_after_call (ps s : store) : Prop :=
  exists k, k <= ps R_R1 /\
    unequal_prefix (strnlen_finalmem ps) (ps R_R0) 0 k /\
    ((k = ps R_R1 /\ s R_R0 = 0) \/
     (k < ps R_R1 /\ s R_R0 = (ps R_R0) ⊕ k /\
      (strnlen_finalmem ps) Ⓑ[(ps R_R0) + k] = 0)) /\
    s V_MEM32 = strnlen_finalmem ps /\ s R_SP = (ps R_SP) ⊖ 16 /\
    s R_R4 = ps R_R0.

Definition strnlen_post (s0 s : store) : Prop :=
  exists k, k <= s0 R_R1 /\
    unequal_prefix (strnlen_finalmem s0) (s0 R_R0) 0 k /\
    ((k = s0 R_R1 /\ s R_R0 = s0 R_R1) \/
     (k < s0 R_R1 /\ s R_R0 = k mod 2^32 /\
      (strnlen_finalmem s0) Ⓑ[(s0 R_R0) + k] = 0)) /\
    s V_MEM32 = strnlen_finalmem s0 /\ s R_SP = (s0 R_SP) ⊖ 8.

Definition strnlen_family (cs ps : store) : invariant_set :=
  fun T Inv Post NoInv s a =>
  match a with
  | 0x5b042 => Inv 0 (s = cs)
  | 0x5b04c => Inv 0 (memchr_scan cs s)
  | 0x5b05c => Inv 0 (memchr_probe cs s)
  | 0x5b072 => Inv 0 (memchr_word_loop cs s)
  | 0x5b092 => Inv 0 (memchr_tail cs s)
  | 0x5b0b0 => Post 0 (memchr_post cs s)
  | 0x5baa4 => Inv 1 (s = ps)
   | 0x5bab4 => Inv 1 (strnlen_after_call cs s)
  | 0x5baba => Post 1 (strnlen_post ps s)
  | _ => NoInv
  end.

Theorem memchr_family_correct :
  forall cs ps t xs (ENTRY : startof t xs = (Addr 0x5b042, cs))
         (MDL : models arm7typctx cs),
    satisfies_all strnlen_program
      (make_invs 0 strnlen_program (strnlen_family cs ps))
      (make_exits 0 strnlen_program (strnlen_family cs ps)) (xs :: t).
Proof.
  intros cs ps t xs ENTRY MDL. apply prove_invs with (t := xs :: t).
  - simpl. rewrite ENTRY. arm7_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
      apply strnlen_program_welltyped.




intro MDL1. clear - PRE MDL1.
    destruct_inv 32 PRE.

    *



simpl in PRE. subst cs.
      do 3 arm7_step. unfold memchr_scan, memchr_frame, memchr_pushmem.
      exists 0. repeat split.
      all: elimstore; psimpl; try assumption; try reflexivity; try lia.
      intros i HI. lia.

    * unfold memchr_scan, memchr_frame in PRE.
      destruct PRE as (k & KN & R0 & R2 & R1 & PREFIX & C & NB & MEM & SP).
      do 2 arm7_step. arm7_step.
      -- arm7_step. arm7_step.
         ++ apply N.eqb_eq in BC0. rewrite !N.mod_small in BC0 by lia.
            assert (k = cs R_R2) by lia. subst k. do 2 arm7_step.
            unfold memchr_tail, memchr_frame. exists (cs R_R2). repeat split.
            all: elimstore; psimpl; try assumption; try reflexivity; try lia.
         ++ apply N.eqb_neq in BC0. unfold memchr_probe, memchr_frame.
            assert (k < cs R_R2).
            { destruct (proj1 (N.le_lteq k (cs R_R2)) KN) as [LT|EQ]; [exact LT|].
              subst k. rewrite !N.mod_small in BC0 by assumption. contradiction. }
            exists k. repeat split; elimstore; psimpl; try assumption; try reflexivity.
      -- arm7_step.
         ++ apply N.eqb_eq in BC0. rewrite !N.mod_small in BC0 by lia.
            assert (k = cs R_R2) by lia. subst k. arm7_step.
            unfold memchr_tail, memchr_frame. exists (cs R_R2). repeat split.
            all: elimstore; psimpl; try assumption; try reflexivity; try lia.
         ++ apply N.eqb_neq in BC0. assert (HK : k < cs R_R2).
            { destruct (proj1 (N.le_lteq k (cs R_R2)) KN) as [LT|EQ]; [exact LT|].
              subst k. rewrite !N.mod_small in BC0 by assumption. contradiction. }
            do 2 arm7_step. arm7_step.
            ** unfold memchr_probe, memchr_frame. exists k. repeat split;
                 elimstore; psimpl; try assumption; try reflexivity; try lia.
            ** do 2 arm7_step. unfold memchr_scan, memchr_frame.
               exists (k+1). repeat split.
               all: elimstore; psimpl; try assumption; try reflexivity; try lia.
               replace (1+k) with (k+1) by lia.
               apply unequal_prefix_succ; try assumption.
               destruct (N.eqb_spec (memchr_pushmem cs Ⓑ[cs R_R0 + k])
                                    (cs R_R1 mod 2^8)); try discriminate; try assumption.
               all: apply N.eqb_neq in BC1; assumption.

    * unfold memchr_probe, memchr_frame in PRE.
      destruct PRE as (k & HK & R0 & R2 & R7 & R1 & PREFIX & C & NB & MEM & SP).
      do 2 arm7_step. arm7_step.
      -- arm7_step. unfold memchr_tail, memchr_frame. exists k. repeat split;
           elimstore; psimpl; try assumption; try reflexivity; try lia.
      -- do 5 arm7_step. unfold memchr_word_loop, memchr_frame, spread_byte32.
         exists k. repeat split.
         all: elimstore; psimpl; try assumption; try reflexivity; try lia.
         ** rewrite land_not3 by assumption. psimpl.
            rewrite (msub_sub 2 (cs R_R2) k) by lia.
            rewrite (msub_sub 32 (cs R_R2) k) by lia.
            rewrite (N.mod_small ((cs R_R2)-k) (2^32)) by lia.
            apply (f_equal (fun x => x mod 2^32)).
            change (2^2) with 4. lia.
         ** rewrite !N.shiftl_mul_pow2. nia.

    * unfold memchr_word_loop, memchr_frame in PRE.
      destruct PRE as (k & KN & R0 & R4 & R6 & R3 & R1 & PREFIX & C & NB & MEM & SP).
      do 2 arm7_step. arm7_step.
      -- do 2 arm7_step. unfold memchr_tail, memchr_frame. exists k.
         repeat split; elimstore; psimpl; try assumption; try reflexivity; try lia.
      -- do 5 arm7_step. arm7_step.
         ++ assert (HK4 : k+4 <= cs R_R2).
            { destruct (N.lt_ge_cases ((cs R_R2)-k) 4) as [LT|GE]; [|lia].
              destruct (0 =? (((cs R_R2)-k) - ((cs R_R2)-k) mod 4)
                          mod 2^32) eqn:E; simpl in BC; try discriminate.
              apply N.eqb_neq in E. exfalso. apply E. psimpl.
              rewrite N.mod_small by lia.
              rewrite (N.mod_small ((cs R_R2)-k) 4) by exact LT. lia. }
            unfold memchr_word_loop, memchr_frame. exists (k+4). repeat split.
            ** exact HK4.
            ** psimpl. reflexivity.
            ** psimpl. clear - HK4. nia.
            ** exact R6.
            ** exact R1.
            ** apply unequal_prefix_word; try assumption.
               unfold zero32 in BC0.
               destruct (zero32 (N.lxor (spread_byte32 (cs R_R1 mod 2^8))
                                        ((memchr_pushmem cs) Ⓓ[(cs R_R0) + k])) =? 0) eqn:Z.
               --- apply N.eqb_eq in Z. unfold zero32 in Z.
                   rewrite (N.lxor_comm (spread_byte32 (cs R_R1 mod 2^8))
                                        ((memchr_pushmem cs) Ⓓ[(cs R_R0) + k])) in Z.
                   exact Z.
               --- unfold zero32 in Z. rewrite Z in BC0. simpl in BC0. discriminate.
            ** exact C.
            ** exact NB.
            ** elimstore. reflexivity.
         ++ do 2 arm7_step. unfold memchr_tail, memchr_frame. exists k.
            repeat split; elimstore; psimpl; try assumption; try reflexivity; try lia.

    * unfold memchr_tail, memchr_frame in PRE.
      destruct PRE as (k & KN & R3 & R2 & R1 & PREFIX & C & NB & MEM & SP).
      arm7_step.
      -- apply N.eqb_eq in BC. rewrite !N.mod_small in BC by lia.
         assert (k = cs R_R2) by lia. subst k. arm7_step.
         unfold memchr_post, memchr_frame. exists (cs R_R2). repeat split.
         all: elimstore; psimpl; try assumption; try reflexivity; try lia.
      -- apply N.eqb_neq in BC. assert (HK : k < cs R_R2).
         { destruct (proj1 (N.le_lteq k (cs R_R2)) KN) as [LT|EQ]; [exact LT|].
           subst k. rewrite !N.mod_small in BC by assumption. contradiction. }
         do 5 arm7_step. arm7_step.
         ++ apply N.eqb_eq in BC0. arm7_step.
            unfold memchr_post, memchr_frame. exists k. repeat split.
            all: elimstore; psimpl; try assumption; try reflexivity; try lia.
            all: try (pose proof (PREFIX i H) as Q; assumption).
         ++ apply N.eqb_neq in BC0. unfold memchr_tail, memchr_frame.
            exists (k+1). repeat split.
            all: elimstore; psimpl; try assumption; try reflexivity; try lia.
            all: try (pose proof (unequal_prefix_succ (memchr_pushmem cs) (cs R_R0)
                                  (cs R_R1 mod 2^8) k PREFIX BC0 i H) as Q; assumption).
            replace (1+k) with (k+1) by lia.
            apply unequal_prefix_succ; assumption.
Qed.
