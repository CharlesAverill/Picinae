(* strnlen -- bounded length of a byte string

   SEMANTICS
   ---------
   strnlen calls memchr for NUL and returns its position, or n when no NUL is
   present.  This proof composes the independently verified memchr theorem with
   the actual caller and callee stack frames.

   SPECIFICATION (POSIX strnlen)
   -----------------------------

     SYNOPSIS
            #include <string.h>
            size_t strnlen(const char *s, size_t maxlen);

     RETURN VALUE
            strnlen returns the first NUL index below maxlen, or maxlen when no
            NUL occurs.  The theorem assumes 0 < s and s+maxlen <= 2^32, so the
            found pointer cannot wrap to NULL.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            strnlen at ELF VA 0x4baa5 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5baa4.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see strnlen_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = s, R1 = maxlen, with 0 < s and s+maxlen <= 2^32.
   Output:  At POP at 0x5baba, there is k <= maxlen with all prior bytes nonzero.
            If k = maxlen then R0 = maxlen; otherwise the byte at k is zero and
            R0 = k.  The exact saved-stack memory and restored SP are specified
            in strnlen_family.v.  The proof stops before POP.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32 armv7_string armv7_memchr memchr_proof strnlen_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition strnlen_entry : addr := 0x5baa4.
Definition strnlen_return : addr := 0x5baba.

Theorem strnlen_correct :
  forall prog (EXT : strnlen_program ⊆2 prog) ps t xs
         (ENTRY : startof t xs = (Addr strnlen_entry, ps))
         (MDL : models arm7typctx ps)
         (VALID : 0 < ps R_R0 /\ ps R_R0 + ps R_R1 <= 2^32),
    satisfies_all prog
      (make_invs 1 strnlen_program (strnlen_family ps ps))
      (make_exits 1 strnlen_program (strnlen_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL VALID.
  eapply satisfies_all_pmono with (p1 := strnlen_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold make_invs, strnlen_family.
    rewrite NOCODE. reflexivity.
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - ps MDL VALID START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply strnlen_program_welltyped.
      intro MDL1. clear - ps VALID PRE MDL1.
      destruct_inv 32 PRE.

      * simpl in PRE. subst ps.
        do 7 arm7_step. set (callee := update _ _ _).
        pose proof (MDL1 R_R0 32 eq_refl) as PN0.
        eapply models_after_steps. eassumption.
          apply strnlen_program_welltyped. intro MDL2.
        eapply (perform_call 0).
        -- reflexivity.
        -- intros. exact (memchr_family_correct callee s1 _ _ ENTRY MDL2).
        -- reflexivity.

      -- intros.
        assert (MDL' : models arm7typctx s').
          eapply preservation_exec_prog; try eassumption.
          apply strnlen_program_welltyped.
        clear - s1 callee VALID PRE PN0 MDL'.
        destruct_inv 32 PRE.
        unfold memchr_post in PRE.
        destruct PRE as (k & KN & PREFIX & POST & NB & MEM & SP).
        assert (C0 : callee R_R0 = s1 R_R0) by (unfold callee; psimpl; reflexivity).
        assert (C1 : callee R_R1 = 0) by (unfold callee; psimpl; reflexivity).
        assert (C2 : callee R_R2 = s1 R_R1) by (unfold callee; psimpl; reflexivity).
        assert (CSP : callee R_SP = (s1 R_SP) ⊖ 16) by (unfold callee; psimpl; reflexivity).
        assert (CM : memchr_pushmem callee = strnlen_finalmem s1).
        { unfold memchr_pushmem, strnlen_finalmem, callee. psimpl. reflexivity. }
        rewrite C2 in KN.
        rewrite C0, C1, CM in PREFIX. rewrite (N.mod_small 0 (2^8)) in PREFIX by lia.
        rewrite C0, C1, C2, CM in POST. rewrite (N.mod_small 0 (2^8)) in POST by lia.
        set (P := (k = s1 R_R1 /\ s' R_R0 = 0 \/
          k < s1 R_R1 /\ s' R_R0 = (s1 R_R0) ⊕ k /\
          (strnlen_finalmem s1) Ⓑ[(s1 R_R0) + k] = 0)) in POST.
        rewrite CM in MEM. rewrite CSP in SP. psimpl in SP.
        arm7_step. unfold strnlen_finalmem. elimstore. psimpl.
        apply NIHere.
        unfold make_invs, strnlen_family, strnlen_program, updateall2, updateall. simpl.
        unfold P in POST. unfold strnlen_after_call. psimpl.
        exists k. split; [exact KN|]. split; [exact PREFIX|].
        split; [exact POST|]. split; [reflexivity|]. split; [reflexivity|].
        apply N.mod_small. exact PN0.

      * unfold strnlen_after_call in PRE.
        destruct PRE as (k & KN & PREFIX & POST & MEM & SP0 & R4).
        destruct (N.eq_dec k (ps R_R1)) as [EQ|NE].
        -- subst k. destruct POST as [(EQ & R0)|(LT & R0 & BYTE)]; [|lia].
           arm7_step.
           ++ do 2 arm7_step.
              eapply NIStep; [reflexivity|reflexivity|]; ISA_symbolic_interp.
              arm7_step.
              unfold strnlen_post, strnlen_finalmem, memchr_pushmem, strnlen_premem.
              exists (ps R_R1). repeat split;
                elimstore; psimpl; try assumption; try reflexivity; try lia.
              all: try (pose proof (PREFIX i H) as Q; assumption).
        -- assert (HK : k < ps R_R1) by lia.
           destruct POST as [POST|POST].
           ++ exfalso. lia.
           ++ destruct POST as (HK' & R0 & BYTE).
              assert (NZ : (ps R_R0) ⊕ k <> 0).
              { destruct VALID as [P0 PN]. psimpl.
                rewrite (N.mod_small (ps R_R0 + k) (2^32)) by lia. lia. }
              arm7_step.
              ** apply N.eqb_eq in BC. contradiction.
              ** arm7_step.
                 eapply NIStep; [reflexivity|reflexivity|]; ISA_symbolic_interp.
                 arm7_step.
                 unfold strnlen_post, strnlen_finalmem, memchr_pushmem, strnlen_premem.
                 exists k. repeat split;
                   elimstore; psimpl; try assumption; try reflexivity; try lia.
                 all: try (pose proof (PREFIX i H) as Q; assumption).
                 right. repeat split; psimpl; try assumption; try reflexivity; try lia.
Qed.
