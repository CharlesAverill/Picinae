(* cfsetspeed -- set input and output termios baud rates

   SEMANTICS
   ---------
   cfsetspeed first calls cfsetospeed with the requested speed.  On the verified
   successful path it then calls cfsetispeed with R1 = 0, the successful result
   of the first call.  Finally it returns the word loaded from its local status
   slot.  The specification preserves the exact behavior if the termios write
   aliases that slot.

   SPECIFICATION (POSIX cfsetspeed)
   --------------------------------

     SYNOPSIS
            #include <termios.h>
            int cfsetspeed(struct termios *tio, speed_t speed);

     RETURN VALUE
            For a valid output speed, and when the termios word does not overlap
            the callees' saved LR or R3 words, R0 is the final word at SP-12 and
            is zero in the ordinary non-aliasing case.  The theorem specifies
            the exact final memory and stops immediately before POP.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            cfsetspeed at ELF VA 0x4c5fd (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5c5fc.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see cfsetspeed_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = tio, R1 = speed.  The speed satisfies cfsetospeed_valid.
            cfsetspeed_safe excludes overlap between tio+8 and the saved LR/R3
            slots needed for the two normal callee returns.
   Output:  At POP at 0x5c60e, R0 is the final word at original SP-12,
            SP = original SP-8, and memory is cfsetspeed_finalmem.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  cfsetospeed_proof cfsetispeed_proof cfsetspeed_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition cfsetspeed_entry : addr := 0x5c5fc.
Definition cfsetspeed_return : addr := 0x5c60e.

Theorem cfsetspeed_correct :
  forall prog (EXT : cfsetspeed_program ⊆2 prog) ps t xs
         (ENTRY : startof t xs = (Addr cfsetspeed_entry, ps))
         (MDL : models arm7typctx ps)
         (VALID : cfsetospeed_valid (ps R_R1) /\ cfsetspeed_safe ps),
    satisfies_all prog
      (make_invs 2 cfsetspeed_program (cfsetspeed_family ps ps))
      (make_exits 2 cfsetspeed_program (cfsetspeed_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL VALID.
  eapply satisfies_all_pmono with (p1 := cfsetspeed_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold make_invs, cfsetspeed_family.
    rewrite NOCODE. reflexivity.
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - ps MDL VALID START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply cfsetspeed_program_welltyped.
      intro MDL1. clear - ps VALID PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst ps. destruct VALID as [SPEED SAFE].
        do 4 arm7_step. set (callee := update _ _ _).
        pose proof (MDL1 R_R0 32 eq_refl) as PN0.
        pose proof (MDL1 R_R3 32 eq_refl) as PN3.
        eapply models_after_steps. eassumption.
          apply cfsetspeed_program_welltyped. intro MDL2.
        eapply (perform_call 0).
        -- reflexivity.
        -- intros. exact (cfsetospeed_family_correct callee s1 _ _ ENTRY MDL2 SPEED).
        -- reflexivity.
        -- intros.
           assert (MDL' : models arm7typctx s').
             eapply preservation_exec_prog; try eassumption.
             apply cfsetspeed_program_welltyped.
           clear - s1 callee SAFE PN0 PN3 PRE MDL'.
           destruct_inv 32 PRE. destruct PRE as (POST & R4P).
           unfold cfsetospeed_post in POST. destruct POST as (R0 & SP & MEM).
           assert (C0 : callee R_R0 = s1 R_R0) by (unfold callee; psimpl; reflexivity).
           assert (C1 : callee R_R1 = s1 R_R1) by (unfold callee; psimpl; reflexivity).
           assert (C4 : callee R_R4 = s1 R_R0) by (unfold callee; psimpl; reflexivity).
           assert (CSP : callee R_SP = (s1 R_SP) ⊖ 16) by (unfold callee; psimpl; reflexivity).
           assert (CF : cfsetospeed_pushmem callee = cfsetspeed_ospeed_frame_mem s1).
           { unfold cfsetspeed_ospeed_frame_mem, cfsetspeed_ospeed_store,
               cfsetspeed_premem, callee. psimpl. reflexivity. }
           rewrite C0, C1, CF in MEM. rewrite CSP in SP. psimpl in SP.
           set (P0 := (s' R_R0 = 0)) in R0.
           set (P4 := (s' R_R4 = callee R_R4)) in R4P.
           eapply NIStep; [reflexivity|reflexivity|]; ISA_symbolic_interp.
           unfold cfsetspeed_safe in SAFE. destruct SAFE as [SAFE20 SAFE24].
           unfold cfsetspeed_after_ospeed_mem, cfsetspeed_ospeed_frame_mem,
             cfsetspeed_ospeed_store, cfsetspeed_premem, cfsetospeed_pushmem.
           psimpl.
           rewrite (cfsetspeed_getmem_frame _ _ _ _ SAFE20).
           rewrite (cfsetspeed_getmem_frame _ _ _ _ SAFE24).
           elimstore; psimpl; try lia.
           arm7_step. unfold P0 in R0. unfold P4 in R4P.
           unfold cfsetspeed_after_ospeed. psimpl.
           split; [exact R0|].
           split; [apply N.mod_small; exact PN3|].
           split; [rewrite R4P; exact C4|].
           split; [reflexivity|].
           unfold cfsetspeed_after_ospeed_mem, cfsetspeed_ospeed_frame_mem,
             cfsetspeed_ospeed_store, cfsetspeed_premem, cfsetospeed_pushmem.
           psimpl. reflexivity.

      * unfold cfsetspeed_after_ospeed in PRE.
        destruct PRE as (R0 & R3 & R4 & SP & MEM).
        destruct VALID as [SPEED SAFE].
        do 5 arm7_step. set (callee := update _ _ _).
        eapply models_after_steps. eassumption.
          apply cfsetspeed_program_welltyped. intro MDL2.
        assert (CV : cfsetispeed_valid (callee R_R1)).
        { unfold cfsetispeed_valid, callee. psimpl. reflexivity. }
        eapply (perform_call 1).
        -- reflexivity.
        -- intros. exact (cfsetispeed_family_correct callee ps _ _ ENTRY MDL2 CV).
        -- reflexivity.
        -- intros.
           assert (MDL' : models arm7typctx s').
             eapply preservation_exec_prog; try eassumption.
             apply cfsetspeed_program_welltyped.
           clear - ps s1 callee SAFE R3 R4 SP MEM PRE MDL'.
           destruct_inv 32 PRE. unfold cfsetispeed_post in PRE.
           destruct PRE as (R00 & SP0 & MEM0).
           assert (C0 : callee R_R0 = ps R_R0) by (unfold callee; psimpl; reflexivity).
           assert (C1 : callee R_R1 = 0) by (unfold callee; psimpl; reflexivity).
           assert (CSP : callee R_SP = (ps R_SP) ⊖ 16) by (unfold callee; psimpl; reflexivity).
           assert (C3 : callee R_R3 = ps R_R3) by (unfold callee; psimpl; exact R3).
           assert (CL : callee R_LR = 0x5c619) by (unfold callee; psimpl; reflexivity).
           assert (CM : callee V_MEM32 = cfsetspeed_before_ispeed_mem ps).
           { unfold callee, cfsetspeed_before_ispeed_mem.
             repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].
             reflexivity. }
           assert (CF : cfsetispeed_pushmem callee = cfsetspeed_ispeed_frame_mem ps).
           { unfold cfsetspeed_ispeed_frame_mem, cfsetispeed_pushmem,
               cfsetspeed_ispeed_store.
             repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].
             rewrite CSP, CL, C3, CM. reflexivity. }
           rewrite C0, C1, CF in MEM0. rewrite CSP in SP0. psimpl in SP0.
           unfold cfsetspeed_safe in SAFE. destruct SAFE as [SAFE20 _].
           assert (LRREAD :
             (setmem 32 LittleE 4 (cfsetspeed_ispeed_frame_mem ps) (8 + ps R_R0)
               (cfsetispeed_newword
                 ((cfsetspeed_ispeed_frame_mem ps) Ⓓ[(ps R_R0) ⊕ 8]) 0)) Ⓓ[(ps R_SP) ⊖ 20]
             = 0x5c619).
           { unfold cfsetspeed_ispeed_frame_mem, cfsetspeed_ispeed_store,
               cfsetispeed_pushmem.
             repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].
             psimpl. rewrite (cfsetspeed_getmem_frame _ _ _ _ SAFE20).
             elimstore. psimpl. reflexivity. }
           set (P0 := (s' R_R0 = 0)) in R00.
           eapply NIStep; [reflexivity|reflexivity|]; ISA_symbolic_interp.
           rewrite LRREAD. psimpl.
           arm7_step. unfold P0 in R00. unfold cfsetspeed_after_ispeed. psimpl.
           split; [exact R00|]. split; [reflexivity|].
           unfold cfsetspeed_finalmem. psimpl. reflexivity.

      * unfold cfsetspeed_after_ispeed in PRE.
        destruct PRE as (R0 & SP & MEM).
        do 4 arm7_step. unfold cfsetspeed_post.
        elimstore. repeat split; psimpl; try assumption; reflexivity.
Qed.
