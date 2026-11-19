(* strlcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strlen)

   SEMANTICS
   ---------
   musl's src/string/strlcpy.c (casts and pointer dereferences written with
   [0] so this comment stays well formed):
       size_t strlcpy(char *d, const char *s, size_t n) {
           char *d0 = d; size_t *wd;
           if (!n--) goto finish;
           if ((s & ALIGN) == (d & ALIGN)) {
               for (; (s & ALIGN) && n && (d[0]=s[0]); n--, s++, d++);
               if (n && s[0]) {
                   wd = d; ws = s;
                   for (; n >= 8 && !HASZERO(ws[0]); n -= 8, ws++, wd++) wd[0] = ws[0];
                   d = wd; s = ws;
               }
           }
           for (; n && (d[0]=s[0]); n--, s++, d++);
           d[0] = 0;
       finish:
           return d - d0 + strlen(s);
       }
   compiled with a 32-byte frame (stp x29,x30,[sp,#-32]! / str x19,[sp,#16]),
   an alignment byte loop (0x15ef1c), a word-at-a-time loop (0x15ef64, 8-byte
   ldr/str with the 0xfefefefefefefeff / 0x8080808080808080 zero test), a
   bounded byte loop (0x15eef0), strb wzr, and bl strlen (0x15efa8, re-proved
   here inside strlcpy_prog as strlen_correct_in_strlcpy).

   SPECIFICATION (strlcpy(3bsd), libbsd / OpenBSD manual)
   ------------------------------------------------------
     SYNOPSIS
            size_t strlcpy(char *dst, const char *src, size_t dstsize);
     DESCRIPTION
            strlcpy() copies up to dstsize - 1 characters from the
            NUL-terminated string src to dst, NUL-terminating the result if
            dstsize is not 0.  If the src and dst strings overlap, the
            behavior is undefined.
     RETURN VALUE
            strlcpy() returns the total length of the string it tried to
            create, that is, the length of src.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strlcpy at 0x5eec4 (ELF vaddr); 0x15eec4 in Ghidra (image base 0x100000);
            callee strlen at 0x5efa8 / 0x15efa8
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strlcpy_armv8.v and
            ../lifted/strlen_armv8.v (combined as strlcpy_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q), X2 = dstsize (n), SP = sp,
            X30 = raddr, X19 = x19, X29 = x29; memory mem.
   PRECONDITION (slc_pre sp mem d q n L K), stated explicitly:
            - q holds a string of length L: bytes q..q+L-1 nonzero, byte q+L = 0;
            - K = min(L, n-1) when n > 0 (K < n, K <= L, and K = L or K + 1 = n);
            - 32 <= sp < 2^64; d+n+32 <= sp and q+L+33 <= sp, i.e. both
              buffers lie below strlcpy's own stack frame (sp-32..sp-1);
              q + n < 2^64;
            - the destination d..d+n-1 does not overlap the source q..q+L
              (q+L < d or d+n <= q).
            Justification: overlapping src/dst is undefined behaviour (see the
            manual above); a destination overlapping strlcpy's own frame is not
            caller-owned memory.  The precondition is needed because strlen
            re-reads the source after the copy and strlcpy reloads X19/X29/X30
            from its frame.
   Output:  If execution reaches the RET (0x15efa4), with
            F = mem with x29, raddr, x19 stored at sp-32, sp-24, sp-16
            (the saved frame, slc_frame):
            X0 = L (= strlen(src));
            memory = F if n = 0, otherwise (bcp F d q K) with byte d+K set to
            0, i.e. src[0..K-1] copied in order to d.. and the terminator
            written at d+K (slc_mem; bcp in lib/GrokStr.v);
            SP = sp, X19 = x19, X29 = x29, X30 = raddr.
            X20..X28 and Z8..Z15 are never written
            (strlcpy_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strlcpy_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
From Grok.proofs Require Import strlcpy_callees.
From Grok.proofs Require strlcpy_vcs_small strlcpy_vcs_loops strlcpy_vcs_word.
Import ARM8Notations.
Open Scope N.

Theorem strlcpy_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x29 L K t xs'
    (PRE0: slc_pre sp mem d q n L K)
    (P1: strlcpy_armv8.strlcpy_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eec4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  pose proof (MDL R_X2 64 eq_refl) as W2. rewrite X2 in W2. simpl in W2.
  assert (PP: strlcpy_prog ⊆2 prog) by (apply strlcpy_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strlcpy_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X29 START PRE0 W19 W29 W30 W0 W1 W2.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlcpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0 W1 W2. rename t1 into t.
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W29, W30, W0, W1, W2. clear WW.
  destruct_inv 64 PRE.
  - eapply strlcpy_vcs_small.slc_case_15eec4; eassumption.
  - eapply strlcpy_vcs_small.slc_case_15eef0; eassumption.
  - eapply strlcpy_vcs_loops.slc_case_15ef1c; eassumption.
  - eapply strlcpy_vcs_loops.slc_case_15ef34; eassumption.
  - eapply strlcpy_vcs_word.slc_case_15ef64; eassumption.
  - eapply strlcpy_vcs_small.slc_case_15ef88; eassumption.
  - eapply strlcpy_vcs_small.slc_case_15ef90; eassumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorem: strlcpy and strlen never write X20..X28 or Z8..Z15.     *)
Theorem strlcpy_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates strlcpy_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
