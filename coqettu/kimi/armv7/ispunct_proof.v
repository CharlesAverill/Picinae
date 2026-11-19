(* ispunct -- test for an ASCII punctuation character

   SEMANTICS
   ---------
   Bytes outside 0x21..0x7e return zero.  Bytes in that range call isalnum and
   negate its Boolean result using CLZ followed by a five-bit logical shift.

   SPECIFICATION (ISO C / POSIX ispunct)
   -------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int ispunct(int c);

     RETURN VALUE
            ispunct returns one exactly for punctuation bytes in the ASCII
            graphic range, and zero otherwise.  The theorem also specifies the
            caller's exact saved-stack memory and stack pointer.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            ispunct at ELF VA 0x3d9d7 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x4d9d6.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see ispunct_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = c.  Start at 0x4d9d6.
   Output:  At POP at 0x4d9e4, R0 = 1 iff c is in 0x21..0x7e and isalnum(c) = 0;
            otherwise R0 = 0.  Memory and SP are described by ispunct_frame.
            The proof stops before POP.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common isalnum_proof ispunct_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition ispunct_entry : addr := 0x4d9d6.
Definition ispunct_return : addr := 0x4d9e4.

Theorem ispunct_correct :
  forall prog (EXT : ispunct_program ⊆2 prog) ps t xs
         (ENTRY : startof t xs = (Addr ispunct_entry, ps))
         (MDL : models arm7typctx ps),
    satisfies_all prog
      (make_invs 1 ispunct_program (ispunct_family ps ps))
      (make_exits 1 ispunct_program (ispunct_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := ispunct_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold make_invs, ispunct_family.
    rewrite NOCODE. reflexivity.
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - ps MDL START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply ispunct_program_welltyped.
      intro MDL1. clear - ps PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst ps.
        do 3 arm7_step. unfold ispunct_cmp_post, ispunct_frame, ispunct_pushmem.
        elimstore. repeat split; psimpl; try reflexivity.
        pose proof (msub_eqb_spec vR_R0 0x21 0x7e) as H.
        specialize (H (ltac:(lia)) (ltac:(lia))).
        change (((vR_R0) ⊖ 0x21 =? 0x5d) = (vR_R0 mod 2^32 =? 0x7e)) in H.
        rewrite H, N.mod_small by assumption. reflexivity.

      * unfold ispunct_cmp_post, ispunct_frame in PRE.
        destruct PRE as (R0 & R3 & CF & ZF & MEM & SP).
        arm7_step.
        solve_range_movhi ((ps R_R0) ⊖ 0x21) 0x5d ispunct_mov_post ispunct_frame.

      * unfold ispunct_mov_post, ispunct_frame in PRE.
        destruct PRE as (R0 & CF & ZF & MEM & SP).
        destruct (N.lt_trichotomy ((ps R_R0) ⊖ 0x21) 0x5d) as [LT|[EQ|GT]].
        -- assert (HLE : ispunct_range (ps R_R0) = true)
             by (unfold ispunct_range; apply N.leb_le; lia).
           assert (HCF : (0x5d <=? (ps R_R0) ⊖ 0x21) = false)
             by (apply N.leb_gt; exact LT).
           assert (HZF : (((ps R_R0) ⊖ 0x21) =? 0x5d) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. unfold ispunct_range in HLE. rewrite HLE in R0. do 2 arm7_step.
           set (callee := update _ _ _).
           eapply models_after_steps. eassumption.
             apply ispunct_program_welltyped. intro MDL2.
           eapply (perform_call 0).
           ++ reflexivity.
           ++ intros. exact (isalnum_family_correct callee ps _ _ ENTRY MDL2).
           ++ reflexivity.
           ++ intros.
              assert (MDL' : models arm7typctx s').
                eapply preservation_exec_prog; try eassumption.
                apply ispunct_program_welltyped.
              clear - ps s1 callee HLE R0 MEM SP PRE MDL'.
              destruct_inv 32 PRE.
              all: unfold isalnum_post, isalnum_frame in PRE.
              all: destruct PRE as (ALNUM & MEM0 & SP0 & LR0).
              all: assert (C0 : callee R_R0 = ps R_R0) by (unfold callee; psimpl; exact R0).
              all: rewrite C0 in ALNUM.
              all: set (P0 := (s' R_R0 =
                if isalnum_test (ps R_R0) then 1 else 0)) in ALNUM.
              all: arm7_step; psimpl.
              all: unfold make_invs, ispunct_family, ispunct_program, updateall2, updateall; simpl.
              all: unfold P0 in ALNUM; unfold callee in MEM0, SP0.
              all: psimpl in MEM0; psimpl in SP0.
              all: unfold ispunct_after_call, ispunct_frame; psimpl.
              all: split; [exact HLE|]; split; [exact ALNUM|].
              all: split; [rewrite MEM0; exact MEM|rewrite SP0; exact SP].

        -- assert (HLE : ispunct_range (ps R_R0) = true)
             by (unfold ispunct_range; apply N.leb_le; lia).
           assert (HCF : (0x5d <=? (ps R_R0) ⊖ 0x21) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((ps R_R0) ⊖ 0x21) =? 0x5d) = true)
             by (apply N.eqb_eq; exact EQ).
           rewrite HCF, HZF in *. unfold ispunct_range in HLE. rewrite HLE in R0. do 2 arm7_step.
           set (callee := update _ _ _).
           eapply models_after_steps. eassumption.
             apply ispunct_program_welltyped. intro MDL2.
           eapply (perform_call 0).
           ++ reflexivity.
           ++ intros. exact (isalnum_family_correct callee ps _ _ ENTRY MDL2).
           ++ reflexivity.
           ++ intros.
              assert (MDL' : models arm7typctx s').
                eapply preservation_exec_prog; try eassumption.
                apply ispunct_program_welltyped.
              clear - ps s1 callee HLE R0 MEM SP PRE MDL'.
              destruct_inv 32 PRE.
              all: unfold isalnum_post, isalnum_frame in PRE.
              all: destruct PRE as (ALNUM & MEM0 & SP0 & LR0).
              all: assert (C0 : callee R_R0 = ps R_R0) by (unfold callee; psimpl; exact R0).
              all: rewrite C0 in ALNUM.
              all: set (P0 := (s' R_R0 =
                if isalnum_test (ps R_R0) then 1 else 0)) in ALNUM.
              all: arm7_step; psimpl.
              all: unfold make_invs, ispunct_family, ispunct_program, updateall2, updateall; simpl.
              all: unfold P0 in ALNUM; unfold callee in MEM0, SP0.
              all: psimpl in MEM0; psimpl in SP0.
              all: unfold ispunct_after_call, ispunct_frame; psimpl.
              all: split; [exact HLE|]; split; [exact ALNUM|].
              all: split; [rewrite MEM0; exact MEM|rewrite SP0; exact SP].

        -- assert (HLE : ispunct_range (ps R_R0) = false)
             by (unfold ispunct_range; apply N.leb_gt; exact GT).
           assert (HCF : (0x5d <=? (ps R_R0) ⊖ 0x21) = true)
             by (apply N.leb_le; lia).
           assert (HZF : (((ps R_R0) ⊖ 0x21) =? 0x5d) = false)
             by (apply N.eqb_neq; lia).
           rewrite HCF, HZF in *. unfold ispunct_range in HLE. rewrite HLE in R0. arm7_step.
           unfold ispunct_post, ispunct_test, ispunct_frame, ispunct_range. rewrite HLE.
           elimstore. repeat split; psimpl; try assumption; reflexivity.

      * unfold ispunct_after_call, ispunct_frame in PRE.
        destruct PRE as (HR & R0 & MEM & SP).
        do 2 arm7_step.
        eapply NIStep; [reflexivity|reflexivity|]; ISA_symbolic_interp.
        arm7_step.
        unfold ispunct_post, ispunct_test, ispunct_frame. rewrite HR.
        destruct (isalnum_test (ps R_R0)) eqn:HT;
          elimstore; repeat split; psimpl; try assumption; reflexivity.
Qed.
