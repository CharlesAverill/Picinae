(* memchr -- find a byte in a bounded array

   SEMANTICS
   ---------
   The implementation scans to an aligned address, compares full words against
   four copies of the target byte, and finishes byte by byte.  The proof tracks
   an unequal prefix and the remaining count through all three strategies.

   SPECIFICATION (ISO C / POSIX memchr)
   ------------------------------------

     SYNOPSIS
            #include <string.h>
            void *memchr(const void *s, int c, size_t n);

     RETURN VALUE
            memchr returns a pointer to the first occurrence of the low byte of c,
            or NULL if it does not occur among the first n bytes.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            memchr at ELF VA 0x4b043 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5b042.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see memchr_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = s, R1 = c, R2 = n.  Start at 0x5b042.
   Output:  At POP at 0x5b0b0, there is k <= n with all prior bytes unequal to
            the low byte of c.  Either k = n and R0 = 0, or k < n, the byte at k
            matches, and R0 = s+k mod 2^32.  Memory contains the five saved stack
            words and SP = initial SP-20.  The proof stops before POP.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32 armv7_string armv7_memchr memchr_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition memchr_entry : addr := 0x5b042.
Definition memchr_return : addr := 0x5b0b0.

Definition memchr_pushmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4
        (setmem 32 LittleE 4
          (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
          ((s0 R_SP) ⊖ 8) (s0 R_R7))
        ((s0 R_SP) ⊖ 12) (s0 R_R6))
      ((s0 R_SP) ⊖ 16) (s0 R_R5))
    ((s0 R_SP) ⊖ 20) (s0 R_R4).

Definition memchr_frame (s0 s : store) : Prop :=
  s0 R_R2 < 2^32 /\ s V_MEM32 = memchr_pushmem s0 /\
  s R_SP = (s0 R_SP) ⊖ 20.

Definition memchr_scan (s0 s : store) : Prop :=
  exists k, k <= s0 R_R2 /\
    s R_R0 = (s0 R_R0) ⊕ k /\ s R_R2 = (s0 R_R2) ⊖ k /\
    s R_R1 = (s0 R_R1) mod 2^8 /\
    unequal_prefix (memchr_pushmem s0) (s0 R_R0) ((s0 R_R1) mod 2^8) k /\
    (s0 R_R1) mod 2^8 < 2^8 /\ memchr_frame s0 s.

Definition memchr_probe (s0 s : store) : Prop :=
  exists k, k < s0 R_R2 /\
    s R_R0 = (s0 R_R0) ⊕ k /\ s R_R2 = (s0 R_R2) ⊖ k /\
    s R_R7 = (s0 R_R0) ⊕ k /\ s R_R1 = (s0 R_R1) mod 2^8 /\
    unequal_prefix (memchr_pushmem s0) (s0 R_R0) ((s0 R_R1) mod 2^8) k /\
    (s0 R_R1) mod 2^8 < 2^8 /\ memchr_frame s0 s.

Definition memchr_word_loop (s0 s : store) : Prop :=
  exists k, k <= s0 R_R2 /\
    s R_R0 = (s0 R_R0) ⊕ k /\
    s R_R4 = ((s0 R_R0) ⊕ k) ⊕
      (((s0 R_R2) - k) - ((s0 R_R2) - k) mod 4) /\
    s R_R6 = (s0 R_R0) ⊕ (s0 R_R2) /\
    s R_R3 = spread_byte32 ((s0 R_R1) mod 2^8) /\
    s R_R1 = (s0 R_R1) mod 2^8 /\
    unequal_prefix (memchr_pushmem s0) (s0 R_R0) ((s0 R_R1) mod 2^8) k /\
    (s0 R_R1) mod 2^8 < 2^8 /\ memchr_frame s0 s.

Definition memchr_tail (s0 s : store) : Prop :=
  exists k, k <= s0 R_R2 /\
    s R_R3 = (s0 R_R0) ⊕ k /\ s R_R2 = (s0 R_R2) ⊖ k /\
    s R_R1 = (s0 R_R1) mod 2^8 /\
    unequal_prefix (memchr_pushmem s0) (s0 R_R0) ((s0 R_R1) mod 2^8) k /\
    (s0 R_R1) mod 2^8 < 2^8 /\ memchr_frame s0 s.

Definition memchr_post (s0 s : store) : Prop :=
  exists k, k <= s0 R_R2 /\
    unequal_prefix (memchr_pushmem s0) (s0 R_R0) ((s0 R_R1) mod 2^8) k /\
    ((k = s0 R_R2 /\ s R_R0 = 0) \/
     (k < s0 R_R2 /\ s R_R0 = (s0 R_R0) ⊕ k /\
      (memchr_pushmem s0) Ⓑ[(s0 R_R0) + k] = (s0 R_R1) mod 2^8)) /\
    memchr_frame s0 s.

Definition memchr_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5b042 => Some (s = s0)
      | 0x5b04c => Some (memchr_scan s0 s)
      | 0x5b05c => Some (memchr_probe s0 s)
      | 0x5b072 => Some (memchr_word_loop s0 s)
      | 0x5b092 => Some (memchr_tail s0 s)
      | 0x5b0b0 => Some (memchr_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition memchr_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? memchr_return
  | _ => false
  end.

Theorem memchr_nwc : forall s1 s2, memchr_armv7 s1 = memchr_armv7 s2.
Proof. reflexivity. Qed.

Theorem memchr_welltyped : welltyped_prog arm7typctx memchr_armv7.
Proof. exact welltyped. Qed.

Theorem memchr_correct :
  forall prog (EXT : memchr_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr memchr_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (memchr_invs s0) memchr_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := memchr_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold memchr_invs.
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
        apply memchr_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst s0.
        do 3 arm7_step. unfold memchr_scan, memchr_frame, memchr_pushmem.
        exists 0. repeat split.
        all: elimstore; psimpl; try assumption; try reflexivity; try lia.
        intros i HI. lia.

      * unfold memchr_scan, memchr_frame in PRE.
        destruct PRE as (k & KN & R0 & R2 & R1 & PREFIX & C & NB & MEM & SP).
        do 2 arm7_step. arm7_step.
        -- arm7_step. arm7_step.
           ++ apply N.eqb_eq in BC0. rewrite !N.mod_small in BC0 by lia.
              assert (k = s0 R_R2) by lia. subst k. do 2 arm7_step.
              unfold memchr_tail, memchr_frame. exists (s0 R_R2). repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
           ++ apply N.eqb_neq in BC0. unfold memchr_probe, memchr_frame.
              assert (k < s0 R_R2).
              { destruct (proj1 (N.le_lteq k (s0 R_R2)) KN) as [LT|EQ]; [exact LT|].
                subst k. rewrite !N.mod_small in BC0 by assumption. contradiction. }
              exists k. repeat split; elimstore; psimpl; try assumption; try reflexivity.
        -- arm7_step.
           ++ apply N.eqb_eq in BC0. rewrite !N.mod_small in BC0 by lia.
              assert (k = s0 R_R2) by lia. subst k. arm7_step.
              unfold memchr_tail, memchr_frame. exists (s0 R_R2). repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
           ++ apply N.eqb_neq in BC0. assert (HK : k < s0 R_R2).
              { destruct (proj1 (N.le_lteq k (s0 R_R2)) KN) as [LT|EQ]; [exact LT|].
                subst k. rewrite !N.mod_small in BC0 by assumption. contradiction. }
              do 2 arm7_step. arm7_step.
              ** unfold memchr_probe, memchr_frame. exists k. repeat split;
                   elimstore; psimpl; try assumption; try reflexivity; try lia.
              ** do 2 arm7_step. unfold memchr_scan, memchr_frame.
                 exists (k+1). repeat split.
                 all: elimstore; psimpl; try assumption; try reflexivity; try lia.
                 replace (1+k) with (k+1) by lia.
                 apply unequal_prefix_succ; try assumption.
                 destruct (N.eqb_spec (s0 V_MEM32 Ⓑ[s0 R_R0 + k])
                                      (s0 R_R1 mod 2^8)); try discriminate; try assumption.
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
              rewrite (msub_sub 2 (s0 R_R2) k) by lia.
              rewrite (msub_sub 32 (s0 R_R2) k) by lia.
              rewrite (N.mod_small ((s0 R_R2)-k) (2^32)) by lia.
              apply (f_equal (fun x => x mod 2^32)).
              change (2^2) with 4. lia.
           ** rewrite !N.shiftl_mul_pow2. nia.

      * unfold memchr_word_loop, memchr_frame in PRE.
        destruct PRE as (k & KN & R0 & R4 & R6 & R3 & R1 & PREFIX & C & NB & MEM & SP).
        do 2 arm7_step. arm7_step.
        -- do 2 arm7_step. unfold memchr_tail, memchr_frame. exists k.
           repeat split; elimstore; psimpl; try assumption; try reflexivity; try lia.
        -- do 5 arm7_step. arm7_step.
           ++ assert (HK4 : k+4 <= s0 R_R2).
              { destruct (N.lt_ge_cases ((s0 R_R2)-k) 4) as [LT|GE]; [|lia].
                destruct (0 =? (((s0 R_R2)-k) - ((s0 R_R2)-k) mod 4)
                            mod 2^32) eqn:E; simpl in BC; try discriminate.
                apply N.eqb_neq in E. exfalso. apply E. psimpl.
                rewrite N.mod_small by lia.
                rewrite (N.mod_small ((s0 R_R2)-k) 4) by exact LT. lia. }
              unfold memchr_word_loop, memchr_frame. exists (k+4). repeat split.
              ** exact HK4.
              ** psimpl. reflexivity.
              ** psimpl. clear - HK4. nia.
              ** exact R6.
              ** exact R1.
              ** apply unequal_prefix_word; try assumption.
                 unfold zero32 in BC0.
                 destruct (zero32 (N.lxor (spread_byte32 (s0 R_R1 mod 2^8))
                                          ((memchr_pushmem s0) Ⓓ[(s0 R_R0) + k])) =? 0) eqn:Z.
                 --- apply N.eqb_eq in Z. unfold zero32 in Z.
                     rewrite (N.lxor_comm (spread_byte32 (s0 R_R1 mod 2^8))
                                          ((memchr_pushmem s0) Ⓓ[(s0 R_R0) + k])) in Z.
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
           assert (k = s0 R_R2) by lia. subst k. arm7_step.
           unfold memchr_post, memchr_frame. exists (s0 R_R2). repeat split.
           all: elimstore; psimpl; try assumption; try reflexivity; try lia.
        -- apply N.eqb_neq in BC. assert (HK : k < s0 R_R2).
           { destruct (proj1 (N.le_lteq k (s0 R_R2)) KN) as [LT|EQ]; [exact LT|].
             subst k. rewrite !N.mod_small in BC by assumption. contradiction. }
           do 5 arm7_step. arm7_step.
           ++ apply N.eqb_eq in BC0. arm7_step.
              unfold memchr_post, memchr_frame. exists k. repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: try (pose proof (PREFIX i H) as Q; assumption).
           ++ apply N.eqb_neq in BC0. unfold memchr_tail, memchr_frame.
              exists (k+1). repeat split.
              all: elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: try (pose proof (unequal_prefix_succ (memchr_pushmem s0) (s0 R_R0)
                                    (s0 R_R1 mod 2^8) k PREFIX BC0 i H) as Q; assumption).
              replace (1+k) with (k+1) by lia.
              apply unequal_prefix_succ; assumption.
Qed.
