From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isalnum_armv7 isalnum_proof ispunct_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition ispunct_program : program := updateall2 ispunct_armv7 isalnum_armv7.

Lemma ispunct_program_contains_ispunct : ispunct_armv7 ⊆2 ispunct_program.
Proof.
  intros s a insn H. unfold ispunct_program, updateall2, updateall, isalnum_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma ispunct_program_contains_isalnum : isalnum_armv7 ⊆2 ispunct_program.
Proof. apply subset_updateall2. Qed.

Theorem ispunct_program_welltyped : welltyped_prog arm7typctx ispunct_program.
Proof.
  intros s a. unfold ispunct_program, updateall2, updateall.
  destruct (isalnum_armv7 s a) as [[sz q]|] eqn:H.
  - pose proof (isalnum_armv7.welltyped s a) as WT. rewrite H in WT. exact WT.
  - apply ispunct_armv7.welltyped.
Qed.

Definition ispunct_range (x : N) : bool := ((x ⊖ 0x21) <=? 0x5d).
Definition ispunct_test (x : N) : bool :=
  if ispunct_range x then negb (isalnum_test x) else false.

Definition ispunct_pushmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
    ((s0 R_SP) ⊖ 8) (s0 R_R3).

Definition ispunct_frame (s0 s : store) : Prop :=
  s V_MEM32 = ispunct_pushmem s0 /\ s R_SP = (s0 R_SP) ⊖ 8.

Definition ispunct_cmp_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s R_R3 = (s0 R_R0) ⊖ 0x21 /\
  s R_CF = (if 0x5d <=? (s0 R_R0) ⊖ 0x21 then 1 else 0) /\
  s R_ZF = (if ((s0 R_R0) ⊖ 0x21) =? 0x5d then 1 else 0) /\
  ispunct_frame s0 s.

Definition ispunct_mov_post (s0 s : store) : Prop :=
  s R_R0 = (if ((s0 R_R0) ⊖ 0x21) <=? 0x5d then s0 R_R0 else 0) /\
  s R_CF = (if 0x5d <=? (s0 R_R0) ⊖ 0x21 then 1 else 0) /\
  s R_ZF = (if ((s0 R_R0) ⊖ 0x21) =? 0x5d then 1 else 0) /\
  ispunct_frame s0 s.

Definition ispunct_after_call (s0 s : store) : Prop :=
  ispunct_range (s0 R_R0) = true /\
  s R_R0 = (if isalnum_test (s0 R_R0) then 1 else 0) /\
  ispunct_frame s0 s.

Definition ispunct_post (s0 s : store) : Prop :=
  s R_R0 = (if ispunct_test (s0 R_R0) then 1 else 0) /\
  ispunct_frame s0 s.

Definition ispunct_family (cs ps : store) : invariant_set :=
  fun T Inv Post NoInv s a =>
  match a with
  | 0x4d936 => Inv 0 (s = cs)
  | 0x4d93a => Inv 0 (isalnum_orr_post cs s)
  | 0x4d93c => Inv 0 (isalnum_sub_post cs s)
  | 0x4d93e => Inv 0 (isalnum_cmp_post cs s)
  | 0x4d940 => Inv 0 (isalnum_digit_entry cs s)
  | 0x4d942 => Inv 0 (isalnum_digit_sub_post cs s)
  | 0x4d944 | 0x4d946 => Inv 0 (isalnum_digit_cmp_post cs s)
  | 0x4d948 => Inv 0 (isalnum_mid cs s)
  | 0x4d94c => Inv 0 (isalnum_early cs s)
  | 0x4d94a | 0x4d94e => Post 0 (isalnum_post cs s)
  | 0x4d9d6 => Inv 1 (s = ps)
  | 0x4d9de => Inv 1 (ispunct_cmp_post ps s)
  | 0x4d9e2 => Inv 1 (ispunct_mov_post ps s)
  | 0x4d9ea => Inv 1 (ispunct_after_call ps s)
  | 0x4d9e4 => Post 1 (ispunct_post ps s)
  | _ => NoInv
  end.

Theorem isalnum_family_correct :
  forall cs ps t xs (ENTRY : startof t xs = (Addr 0x4d936, cs))
         (MDL : models arm7typctx cs),
    satisfies_all ispunct_program
      (make_invs 0 ispunct_program (ispunct_family cs ps))
      (make_exits 0 ispunct_program (ispunct_family cs ps)) (xs :: t).
Proof.
  intros cs ps t xs ENTRY MDL. apply prove_invs with (t := xs :: t).
  - simpl. rewrite ENTRY. arm7_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
      apply ispunct_program_welltyped.
    intro MDL1. clear - PRE MDL1.
    destruct_inv 32 PRE.

    * simpl in PRE. subst cs.
      arm7_step. unfold isalnum_orr_post, isalnum_frame.
      elimstore. repeat split; psimpl; reflexivity.

    * unfold isalnum_orr_post, isalnum_frame in PRE.
      destruct PRE as (R0 & R3 & MEM & SP & LR).
      arm7_step. unfold isalnum_sub_post, isalnum_frame.
      elimstore. repeat split; psimpl; try assumption; try reflexivity;
        rewrite <- ?R3; reflexivity.

    * unfold isalnum_sub_post, isalnum_frame in PRE.
      destruct PRE as (R0 & R3 & MEM & SP & LR).
      arm7_step. unfold isalnum_cmp_post, isalnum_frame.
      elimstore. repeat split; psimpl; try assumption; try reflexivity.
      pose proof (msub_eqb_spec ((cs R_R0) .| 0x20) 0x61 0x7a) as H.
      specialize (H (ltac:(lia)) (ltac:(lia))).
      change ((((cs R_R0) .| 0x20) ⊖ 0x61 =? 0x19) =
              (((cs R_R0) .| 0x20) mod 2^32 =? 0x7a)) in H.
      rewrite H, <- ?R3. reflexivity.

    * unfold isalnum_cmp_post, isalnum_frame in PRE.
      destruct PRE as (R0 & R3 & CF & ZF & MEM & SP & LR).
      destruct (N.lt_trichotomy (((cs R_R0) .| 0x20) ⊖ 0x61) 0x19)
        as [LT|[EQ|GT]].
      -- assert (HLE : (((cs R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = true)
           by (apply N.leb_le; lia).
         assert (HCF : (0x19 <=? ((cs R_R0) .| 0x20) ⊖ 0x61) = false)
           by (apply N.leb_gt; exact LT).
         assert (HZF : (((cs R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = false)
           by (apply N.eqb_neq; lia).
         rewrite HCF, HZF in *. arm7_step.
         unfold isalnum_early, isalnum_test, isalnum_alpha, isalnum_frame.
         rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
      -- assert (HLE : (((cs R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = true)
           by (apply N.leb_le; lia).
         assert (HCF : (0x19 <=? ((cs R_R0) .| 0x20) ⊖ 0x61) = true)
           by (apply N.leb_le; lia).
         assert (HZF : (((cs R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = true)
           by (apply N.eqb_eq; exact EQ).
         rewrite HCF, HZF in *. arm7_step.
         unfold isalnum_early, isalnum_test, isalnum_alpha, isalnum_frame.
         rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
      -- assert (HLE : (((cs R_R0) .| 0x20) ⊖ 0x61 <=? 0x19) = false)
           by (apply N.leb_gt; exact GT).
         assert (HCF : (0x19 <=? ((cs R_R0) .| 0x20) ⊖ 0x61) = true)
           by (apply N.leb_le; lia).
         assert (HZF : (((cs R_R0) .| 0x20) ⊖ 0x61 =? 0x19) = false)
           by (apply N.eqb_neq; lia).
         rewrite HCF, HZF in *. arm7_step.
         unfold isalnum_digit_entry, isalnum_alpha, isalnum_frame.
         rewrite HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

    * unfold isalnum_digit_entry, isalnum_frame in PRE.
      destruct PRE as (R0 & HA & MEM & SP & LR).
      arm7_step. unfold isalnum_digit_sub_post, isalnum_frame.
      elimstore. repeat split; psimpl; try assumption; reflexivity.

    * unfold isalnum_digit_sub_post, isalnum_frame in PRE.
      destruct PRE as (R0 & HA & MEM & SP & LR).
      arm7_step. unfold isalnum_digit_cmp_post, isalnum_frame.
      elimstore. repeat split; psimpl; try assumption; try reflexivity.
      pose proof (msub_eqb_spec (cs R_R0) 0x30 0x39) as H.
      specialize (H (ltac:(lia)) (ltac:(lia))).
      change (((cs R_R0) ⊖ 0x30 =? 0x9) = (cs R_R0 mod 2^32 =? 0x39)) in H.
      rewrite H, <- ?R0. reflexivity.

    * unfold isalnum_digit_cmp_post, isalnum_frame in PRE.
      destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
      arm7_step. unfold isalnum_digit_cmp_post, isalnum_frame.
      elimstore. repeat split; assumption.

    * unfold isalnum_digit_cmp_post, isalnum_frame in PRE.
      destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
      solve_range_movhi ((cs R_R0) ⊖ 0x30) 0x9 isalnum_mid isalnum_frame.

    * unfold isalnum_mid, isalnum_frame in PRE.
      destruct PRE as (R0 & CF & ZF & HA & MEM & SP & LR).
      destruct (N.lt_trichotomy ((cs R_R0) ⊖ 0x30) 0x9) as [LT|[EQ|GT]].
      -- assert (HLE : ((cs R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
         assert (HCF : (0x9 <=? (cs R_R0) ⊖ 0x30) = false) by (apply N.leb_gt; exact LT).
         assert (HZF : ((cs R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
         rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
         unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
         rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
      -- assert (HLE : ((cs R_R0) ⊖ 0x30 <=? 0x9) = true) by (apply N.leb_le; lia).
         assert (HCF : (0x9 <=? (cs R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
         assert (HZF : ((cs R_R0) ⊖ 0x30 =? 0x9) = true) by (apply N.eqb_eq; exact EQ).
         rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
         unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
         rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.
      -- assert (HLE : ((cs R_R0) ⊖ 0x30 <=? 0x9) = false) by (apply N.leb_gt; exact GT).
         assert (HCF : (0x9 <=? (cs R_R0) ⊖ 0x30) = true) by (apply N.leb_le; lia).
         assert (HZF : ((cs R_R0) ⊖ 0x30 =? 0x9) = false) by (apply N.eqb_neq; lia).
         rewrite HCF, HZF in *. rewrite HLE in R0. arm7_step.
         unfold isalnum_post, isalnum_test, isalnum_digit, isalnum_frame.
         rewrite HA, HLE. elimstore. repeat split; psimpl; try assumption; reflexivity.

    * unfold isalnum_early, isalnum_frame in PRE.
      destruct PRE as (HT & MEM & SP & LR).
      arm7_step. unfold isalnum_post, isalnum_frame. rewrite HT.
      elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
