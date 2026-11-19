(* ldiv -- 32-bit signed quotient/remainder structure writer.
   Entry 0x5a60a: R0 points to the result, R1/R2 are numerator/divisor,
   with R2 nonzero.  At POP 0x5a61c, R0 = original R0, quotient and
   remainder have been stored at offsets 0 and 4, and memory/SP/LR are exact. *)

From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  ldiv_armv7 signed_div_spec signed_div_family divmod_family divmod_proof ldiv_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition ldiv_entry_addr : addr := 0x5a60a.

Theorem ldiv_correct :
  forall prog (EXT : ldiv_program ⊆2 prog) ps t xs
    (ENTRY : startof t xs = (Addr ldiv_entry_addr, ps))
    (MDL : models arm7typctx ps)
    (NONZERO : ps R_R2 <> 0),
  satisfies_all prog
    (make_invs 4 ldiv_program (ldiv_family ps ps))
    (make_exits 4 ldiv_program (ldiv_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL NONZERO.
  eapply satisfies_all_pmono with (p1 := ldiv_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE.
    unfold make_invs, ldiv_family, divmod_family, signed_div_family.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - ps MDL NONZERO START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply ldiv_program_welltyped.
      intro MDL1. clear - ps NONZERO PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst ps. rename s1 into s0.
      do 5 arm7_step. set (callee := update _ _ _).
      assert (C0 : callee R_R0 = s0 R_R1) by (unfold callee; psimpl; reflexivity).
      assert (C1 : callee R_R1 = s0 R_R2) by (unfold callee; psimpl; reflexivity).
      assert (C4 : callee R_R4 = s0 R_R0) by (unfold callee; psimpl; reflexivity).
      assert (CSP : callee R_SP = (s0 R_SP) ⊖ 8) by (unfold callee; psimpl; reflexivity).
      assert (CLR : callee R_LR = 0x5a617) by (unfold callee; psimpl; reflexivity).
      assert (CM : callee V_MEM32 = ldiv_pushmem s0) by (unfold callee; psimpl; reflexivity).
      assert (CNZ : callee R_R1 <> 0) by (rewrite C1; exact NONZERO).
      eapply models_after_steps. eassumption.
        apply ldiv_program_welltyped. intro MDL2.
      eapply (perform_call 2 4 eq_refl (ldiv_family s0 s0)
        (divmod_family callee callee) ldiv_program).
      * intros. exact (divmod_correct ldiv_program ldiv_program_contains_divmod
          callee _ _ ENTRY MDL2 CNZ).
      * reflexivity.
      * intros a' s' t2 ENTRY2 XP UT PRE.
        clear - s0 callee C0 C1 C4 CSP CLR CM PRE.
        destruct_inv 32 PRE.
        unfold divmod_post in PRE.
        destruct PRE as (Q & R & MEM & SP & LR & R4).
        rewrite C0, C1 in Q, R. rewrite C4 in R4.
        rewrite CSP in SP. rewrite CLR in LR.
        assert (CMEM : divmod_pushmem callee = ldiv_callmem s0).
        { unfold divmod_pushmem, ldiv_callmem. rewrite C0, C1, CSP, CLR, CM. reflexivity. }
        rewrite CMEM in MEM.
        do 4 arm7_step.
        unfold ldiv_post, ldiv_finalmem. repeat split;
          try assumption; try reflexivity.
Qed.
