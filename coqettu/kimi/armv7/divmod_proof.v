(* Signed quotient/remainder wrapper from ld-musl-armhf.so.1.
   Entry 0x306fc requires a nonzero divisor in R1.  At BX LR, R0 is the
   signed quotient and R1 is the original numerator minus divisor*quotient.
   The three push words remain in memory; SP and LR are restored. *)

From Stdlib Require Import NArith Lia FunctionalExtensionality.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  FUN_0003046e_armv7 FUN_000306fc_armv7 signed_div_spec signed_div_family
  signed_div_proof divmod_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition divmod_entry_addr : addr := 0x306fc.

Theorem divmod_correct :
  forall prog (EXT : divmod_program ⊆2 prog) ps t xs
    (ENTRY : startof t xs = (Addr divmod_entry_addr, ps))
    (MDL : models arm7typctx ps)
    (NONZERO : ps R_R1 <> 0),
  satisfies_all prog
    (make_invs 2 divmod_program (divmod_family ps ps))
    (make_exits 2 divmod_program (divmod_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL NONZERO.
  eapply satisfies_all_pmono with (p1 := divmod_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold make_invs, divmod_family, signed_div_family.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    pose proof (MDL R_R0 32 eq_refl) as PA32.
    pose proof (MDL R_R1 32 eq_refl) as PB32.
    pose proof (MDL R_SP 32 eq_refl) as PSP32.
    pose proof (MDL R_LR 32 eq_refl) as PLR32.
    clear - ps MDL NONZERO PA32 PB32 PSP32 PLR32 START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply divmod_program_welltyped.
      intro MDL1. clear - ps NONZERO PA32 PB32 PSP32 PLR32 PRE MDL1.
      destruct_inv 32 PRE.
      all: try contradiction.
      simpl in PRE. subst ps. rename s1 into s0.
      assert (Z0 : (s0 R_R1 =? 0) = false) by (apply N.eqb_neq; exact NONZERO).
      arm7_step. rewrite Z0 in *.
      arm7_step. all: try discriminate BC. do 2 arm7_step.
      set (callee := update _ _ _).
      assert (CNZ : callee R_R1 <> 0)
        by (unfold callee; psimpl; exact NONZERO).
      assert (CNF : callee R_NF = callee R_R1 >> 31).
      { unfold callee. psimpl. rewrite msub_0_r, N.mod_small by exact PB32.
        rewrite slt32_nf by exact PB32. reflexivity. }
      eapply models_after_steps. eassumption.
        apply divmod_program_welltyped. intro MDL2.
      eapply (perform_call 1 2 eq_refl (divmod_family s0 s0)
        (signed_div_family callee callee) divmod_program).
      * intros. exact (signed_div_correct divmod_program (fun s a x H => H)
          callee _ _ ENTRY MDL2 CNZ CNF).
      * reflexivity.
      * intros a' s' t2 ENTRY2 XP UT PRE.
        clear - s0 callee PA32 PB32 PSP32 PLR32 PRE.
        destruct_inv 32 PRE.
        all: unfold signed_div_post, signed_div_frame in PRE.
        all: destruct PRE as (SQ & MEM & SP & LR & R4C).
        all: assert (C0 : callee R_R0 = s0 R_R0)
          by (unfold callee; psimpl; reflexivity).
        all: assert (C1 : callee R_R1 = s0 R_R1)
          by (unfold callee; psimpl; reflexivity).
        all: assert (C4 : callee R_R4 = s0 R_R4)
          by (unfold callee; psimpl; reflexivity).
        all: rewrite C0, C1 in SQ.
        all: unfold callee in MEM, SP, LR.
        all: psimpl in MEM.
        all: psimpl in SP.
        all: psimpl in LR.
        all: do 4 arm7_step.
        all: unfold divmod_post, signed_remainder, divmod_pushmem.
        all: elimstore; repeat split; psimpl; try assumption; try reflexivity;
          try (rewrite R4C; exact C4).
        all: rewrite N.mod_small by assumption.
        all: reflexivity.
Qed.
