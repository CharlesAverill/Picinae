(* strrchr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strlen, tail-calls memrchr)

   SEMANTICS
   ---------
   musl's src/string/strrchr.c:
       return __memrchr(s, c, strlen(s) + 1);
   The binary pushes a 48-byte frame (X29, X30 at sp-48/sp-40, X19 at
   sp-32, the 32-bit c at sp-4), keeps s in X19, calls strlen (0x15efa8),
   reloads c, sets X2 = strlen(s) + 1, X0 = s, restores X19/X29/X30 and SP,
   and tail-calls memrchr (b 0x15e83c).  strlen's whole proof
   (strlen_proof.v) is reused via lib/GrokCall.v (satisfies_all_transfer),
   with X19 = s carried across the call by lib/GrokKeep.v; memrchr's
   invariants (memrchr_defs.v) are instantiated at level 1 and its VCs are
   closed with the shared closers of memrchr_lib.v.

   SPECIFICATION (man 3 strrchr, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <string.h>
            char *strrchr(const char *s, int c);

     DESCRIPTION
            The strrchr() function returns a pointer to the last occurrence
            of the character c in the string s.
            Here "character" means "byte"; these functions do not work with
            wide or multibyte characters.

     RETURN VALUE
            The strrchr() function returns a pointer to the matched
            character or NULL if the character is not found.  The
            terminating null byte is considered part of the string, so that
            if c is specified as '\0', these functions return a pointer to
            the terminator.

   THEOREM AND PRECONDITIONS
   -------------------------
   strrchr_partial_correctness:
   - k is the length of s in the memory seen by strlen, i.e. after the
     frame is pushed (rr_frame: mem with x29, raddr, x19, c stored at
     sp-48, sp-40, sp-32, sp-4); this equals the entry memory whenever the
     string does not overlap [sp-48, sp).  n = k + 1.
   - memrchr's scalar-path precondition: 0 < s, s + n < 2^64 and
     (n <= 14 or (s + n) mod 16 <> 0); the NEON block path of memrchr is not
     verified (see memrchr_proof.v).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strrchr at 0x5f228 (ELF vaddr); 0x15f228 in Ghidra (image base 0x100000);
            callees strlen 0x15efa8, memrchr 0x15e83c.
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strrchr_armv8.v,
            memrchr_armv8.v, strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = p, X1 = c; X30 = raddr, SP = sp, X19 = x19, X29 = x29;
            mem = memory on entry.  Let m' = rr_frame sp mem raddr x19 x29 c
            and c8 = c mod 2^8 (= c8 (c mod 2^32), memrchr_lib.c8_32).
   Output:  At memrchr's RET (0x15e948; mrc_post at level 1): memory = m',
            SP = sp, X30 = raddr, X19 = x19, X29 = x29, and either
            X0 = p + j for some j < n with m'[p+j] = c8 and no byte equal to c8
            in [p+j+1, p+n), or X0 = 0 and no byte equal to c8 in [p, p+n).
            (Bytes [p, p+n) are the string including its terminator.)
            X20..X28 and Z8..Z15 are never written by strrchr, strlen or
            memrchr (strrchr_preserves_other_callee_saved).
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strrchr_armv8 memrchr_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require Import strlen_proof memrchr_defs memrchr_lib strrchr_defs strrchr_callees.
Import ARM8Notations.
Open Scope N.

Theorem strrchr_partial_correctness:
  ∀ prog s sp mem raddr x19 x29 p c n k t xs'
    (P2: strrchr_armv8.strrchr_armv8 ⊆2 prog) (P1: memrchr_armv8.memrchr_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f228, s)) (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p) (X1: s R_X1 = c)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29)
    (NF: nilfree (rr_frame sp mem raddr x19 x29 c) p k) (NZ: rr_frame sp mem raddr x19 x29 c Ⓑ[p + k] = 0)
    (KN: n = k + 1) (PP: 0 < p) (PN: p + n < 2^64) (NEON: n <= 14 \/ (p + n) mod 16 <> 0),
  satisfies_all prog (invs1 sp mem raddr x19 x29 p c n) (exits1 sp mem raddr x19 x29 p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=rr_prog).
    apply rr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X29 NF NZ KN PP PN NEON START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply rr_prog_welltyped. intro MDL1.
  clear - PRE MDL1 NF NZ KN PP PN NEON. rename t1 into t.
  destruct_inv 64 PRE.
  - (* memrchr entry 0x15e83c *)
    clear NF NZ KN PP PN NEON.
    destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & PP & PN & NEON & X19 & X29).
    repeat grok_step; try match goal with H: models _ _ |- _ => clear H end; bools_to_props_mr.
    all: first [ solve [mrc_neon NEON] | solve [mrc_enter n] ].
  - (* memrchr loop 0x15e924 *)
    clear NF NZ KN PP PN NEON.
    destruct PRE as (j & JN & X2 & X4 & X1 & PP & PN & NM & MEM & SP & X30 & X19 & X29).
    repeat grok_step; try match goal with H: models _ _ |- _ => clear H end; bools_to_props_mr.
    all: first [ solve [mrc_null j NM BC] | solve [mrc_found j NM BC BC0] | solve [mrc_next j NM BC BC0] ].
  - (* strrchr entry 0x15f228 *)
    destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X29).
    pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
    pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
    pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
    pose proof (MDL1 R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
    pose proof (MDL1 R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
    do 6 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply rr_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply strlen_correct_in_strrchr; first [ eassumption | reflexivity ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply rr_prog_welltyped.
    set (t' := t2++t0++_::t) in *. clearbody s2 t'.
    clear - PRE MDL' SP64 P64 C64 R64 W29 W19 NF NZ KN PP PN NEON.
    rename MDL' into MDL. rename s' into s.
    destruct_inv 64 PRE.
    destruct PRE as ((k' & KLT & R0 & NF' & Z & MEM & SP & X30) & XR19).
    assert (k' = k) by (eapply strlen_post_unique; eassumption).
    subst k'.
    unfold rr_mem, rr_frame in MEM.
    repeat arm8_step.
    repeat split; try reflexivity; try assumption;
      first [ apply N.mod_small; assumption | rewrite KN, N.add_comm; apply N.mod_small; lia ].
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X19/X29/X30 are never
   written by strrchr, strlen or memrchr. *)
Theorem strrchr_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates rr_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
