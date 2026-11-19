From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  cfsetospeed_armv7 cfsetospeed_proof cfsetispeed_armv7 cfsetispeed_proof cfsetspeed_armv7.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition cfsetspeed_program : program :=
  updateall2 cfsetspeed_armv7 (updateall2 cfsetospeed_armv7 cfsetispeed_armv7).

Lemma cfsetspeed_program_contains_cfsetspeed : cfsetspeed_armv7 ⊆2 cfsetspeed_program.
Proof.
  intros s a insn H.
  unfold cfsetspeed_program, updateall2, updateall, cfsetospeed_armv7, cfsetispeed_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma cfsetspeed_program_contains_cfsetospeed : cfsetospeed_armv7 ⊆2 cfsetspeed_program.
Proof.
  intros s a insn H.
  unfold cfsetspeed_program, updateall2, updateall,
    cfsetspeed_armv7, cfsetospeed_armv7, cfsetispeed_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma cfsetspeed_program_contains_cfsetispeed : cfsetispeed_armv7 ⊆2 cfsetspeed_program.
Proof.
  intros s a insn H.
  unfold cfsetspeed_program, updateall2, updateall,
    cfsetspeed_armv7, cfsetospeed_armv7, cfsetispeed_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem cfsetspeed_program_welltyped : welltyped_prog arm7typctx cfsetspeed_program.
Proof.
  intros s a. unfold cfsetspeed_program, updateall2, updateall.
  destruct (cfsetispeed_armv7 s a) as [[sz q]|] eqn:H.
  - pose proof (cfsetispeed_armv7.welltyped s a) as WT. rewrite H in WT. exact WT.
  - destruct (cfsetospeed_armv7 s a) as [[sz q]|] eqn:HO.
    + pose proof (cfsetospeed_armv7.welltyped s a) as WT. rewrite HO in WT. exact WT.
    + apply cfsetspeed_armv7.welltyped.
Qed.

Definition cfsetspeed_premem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
    ((s0 R_SP) ⊖ 8) (s0 R_R4).

Definition cfsetspeed_ospeed_store (s0 : store) : store :=
  s0[R_R4 := s0 R_R0][R_SP := (s0 R_SP) ⊖ 16]
    [V_MEM32 := cfsetspeed_premem s0][R_LR := 0x5c607][R_T := 1].

Definition cfsetspeed_ospeed_frame_mem (s0 : store) : memory :=
  cfsetospeed_pushmem (cfsetspeed_ospeed_store s0).

Definition cfsetspeed_after_ospeed_mem (s0 : store) : memory :=
  setmem 32 LittleE 4 (cfsetspeed_ospeed_frame_mem s0)
    ((s0 R_R0) ⊕ 8)
    (cfsetospeed_newword
      ((cfsetspeed_ospeed_frame_mem s0) Ⓓ[(s0 R_R0) ⊕ 8]) (s0 R_R1)).

Definition cfsetspeed_before_ispeed_mem (s0 : store) : memory :=
  setmem 32 LittleE 4 (cfsetspeed_after_ospeed_mem s0) ((s0 R_SP) ⊖ 12) 0.

Definition cfsetspeed_ispeed_store (s0 : store) : store :=
  s0[R_R0 := s0 R_R0][R_R1 := 0][R_R4 := s0 R_R0]
    [R_SP := (s0 R_SP) ⊖ 16][V_MEM32 := cfsetspeed_before_ispeed_mem s0]
    [R_LR := 0x5c619][R_T := 1].

Definition cfsetspeed_ispeed_frame_mem (s0 : store) : memory :=
  cfsetispeed_pushmem (cfsetspeed_ispeed_store s0).

Definition cfsetspeed_finalmem (s0 : store) : memory :=
  setmem 32 LittleE 4 (cfsetspeed_ispeed_frame_mem s0)
    ((s0 R_R0) ⊕ 8)
    (cfsetispeed_newword
      ((cfsetspeed_ispeed_frame_mem s0) Ⓓ[(s0 R_R0) ⊕ 8]) 0).

Definition cfsetspeed_after_ospeed (s0 s : store) : Prop :=
  s R_R0 = 0 /\ s R_R3 = s0 R_R3 /\ s R_R4 = s0 R_R0 /\
  s R_SP = (s0 R_SP) ⊖ 16 /\ s V_MEM32 = cfsetspeed_after_ospeed_mem s0.

Definition cfsetspeed_after_ispeed (s0 s : store) : Prop :=
  s R_R0 = 0 /\ s R_SP = (s0 R_SP) ⊖ 16 /\
  s V_MEM32 = cfsetspeed_finalmem s0.

Definition cfsetspeed_word_disjoint (a b : N) : Prop :=
  4 <= a ⊖ b /\ 4 <= b ⊖ a.

Lemma cfsetspeed_getmem_frame (m : memory) (a b v : N) :
  cfsetspeed_word_disjoint a b ->
  (setmem 32 LittleE 4 m a v) Ⓓ[b] = m Ⓓ[b].
Proof.
  intros [H1 H2]. apply getmem_frame; [left; exact H1|left; exact H2].
Qed.

Definition cfsetspeed_safe (s0 : store) : Prop :=
  cfsetspeed_word_disjoint (8 + s0 R_R0) ((s0 R_SP) ⊖ 20) /\
  cfsetspeed_word_disjoint (8 + s0 R_R0) ((s0 R_SP) ⊖ 24).

Definition cfsetspeed_post (s0 s : store) : Prop :=
  s R_R0 = (cfsetspeed_finalmem s0) Ⓓ[(s0 R_SP) ⊖ 12] /\
  s R_SP = (s0 R_SP) ⊖ 8 /\ s V_MEM32 = cfsetspeed_finalmem s0.

Definition cfsetspeed_family (cs ps : store) : invariant_set :=
  fun T Inv Post NoInv s a =>
  match a with
  | 0x5c59a => Inv 0 (s = cs /\ cfsetospeed_valid (cs R_R1))
  | 0x5c5ba => Post 0 (cfsetospeed_post cs s /\ s R_R4 = cs R_R4)
  | 0x5c5cc => Inv 1 (s = cs /\ cfsetispeed_valid (cs R_R1))
  | 0x5c5ea => Post 1 (cfsetispeed_post cs s)
  | 0x5c5fc => Inv 2 (s = ps)
  | 0x5c606 => Inv 2 (cfsetspeed_after_ospeed ps s)
  | 0x5c618 => Inv 2 (cfsetspeed_after_ispeed ps s)
  | 0x5c60e => Post 2 (cfsetspeed_post ps s)
  | _ => NoInv
  end.

Theorem cfsetospeed_family_correct :
  forall cs ps t xs (ENTRY : startof t xs = (Addr 0x5c59a, cs))
         (MDL : models arm7typctx cs)
         (VALID : cfsetospeed_valid (cs R_R1)),
    satisfies_all cfsetspeed_program
      (make_invs 0 cfsetspeed_program (cfsetspeed_family cs ps))
      (make_exits 0 cfsetspeed_program (cfsetspeed_family cs ps)) (xs :: t).
Proof.
  intros cs ps t xs ENTRY MDL VALID. apply prove_invs with (t := xs :: t).
  - simpl. rewrite ENTRY. arm7_step. split; [reflexivity|exact VALID].
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
      apply cfsetspeed_program_welltyped.
    intro MDL1. clear - PRE MDL1.
    destruct_inv 32 PRE.
    * destruct PRE as [EQ VALID]. simpl in EQ. subst cs.
      do 4 arm7_step. unfold cfsetospeed_valid in VALID.
      rewrite VALID. arm7_step. do 6 arm7_step.
      unfold cfsetospeed_post, cfsetospeed_newword, cfsetospeed_pushmem.
      elimstore. repeat split; psimpl; reflexivity.
Qed.

Theorem cfsetispeed_family_correct :
  forall cs ps t xs (ENTRY : startof t xs = (Addr 0x5c5cc, cs))
         (MDL : models arm7typctx cs)
         (VALID : cfsetispeed_valid (cs R_R1)),
    satisfies_all cfsetspeed_program
      (make_invs 1 cfsetspeed_program (cfsetspeed_family cs ps))
      (make_exits 1 cfsetspeed_program (cfsetspeed_family cs ps)) (xs :: t).
Proof.
  intros cs ps t xs ENTRY MDL VALID. apply prove_invs with (t := xs :: t).
  - simpl. rewrite ENTRY. arm7_step. split; [reflexivity|exact VALID].
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
      apply cfsetspeed_program_welltyped.
    intro MDL1. clear - PRE MDL1.
    destruct_inv 32 PRE.
    * destruct PRE as [EQ VALID]. simpl in EQ. subst cs.
      do 4 arm7_step. unfold cfsetispeed_valid in VALID.
      change (s1 R_R1 .& 4294963199 .& 4294967280 = 0) in VALID.
      rewrite VALID. arm7_step.
      -- simpl in BC. discriminate.
      -- do 5 arm7_step.
         unfold cfsetispeed_post, cfsetispeed_newword, cfsetispeed_pushmem.
         elimstore. repeat split; psimpl; reflexivity.
Qed.
