(* stpncpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls memset)

   SEMANTICS
   ---------
   musl's src/string/stpncpy.c (casts dropped and pointer dereferences
   written with [0] so this comment stays well formed):
       char *__stpncpy(char *restrict d, const char *restrict s, size_t n) {
           word *wd; const word *ws;
           if ((s & ALIGN) == (d & ALIGN)) {
               for (; (s & ALIGN) && n && (d[0]=s[0]); n--, s++, d++);
               if (!n || !s[0]) goto tail;
               wd = d; ws = s;
               for (; n >= 8 && !HASZERO(ws[0]); n -= 8, ws++, wd++) wd[0] = ws[0];
               d = wd; s = ws;
           }
           for (; n && (d[0]=s[0]); n--, s++, d++);
       tail:
           memset(d, 0, n);
           return d;
       }
       weak_alias(__stpncpy, stpncpy);
   compiled with a 32-byte frame (stp x29,x30,[sp,#-32]! / str x19,[sp,#16]),
   an alignment byte loop (0x15e9ec), a word-at-a-time loop (0x15ea38, 8-byte
   ldr/str with the 0xfefefefefefefeff / 0x8080808080808080 zero test), a
   byte loop (0x15ea64), and bl memset (0x118400, re-proved here inside
   stp_prog as memset_correct_in_stpncpy, all paths but DC ZVA, carrying X19 across the call).

   SPECIFICATION (man 3 stpncpy, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            char *stpncpy(char dst[restrict .dsize], const char *restrict src,
                          size_t dsize);
     DESCRIPTION
            These functions copy non-null bytes from the string pointed to by
            src into the array pointed to by dst.  If the source has too few
            non-null bytes to fill the destination, the functions pad the
            destination with trailing null bytes.  If the destination buffer,
            limited by its size, isn't large enough to hold the copy, the
            resulting character sequence is truncated.
            An implementation of these functions might be:
                dlen = strnlen(src, dsize);
                return memset(mempcpy(dst, src, dlen), 0, dsize - dlen);
     RETURN VALUE
            stpncpy() returns a pointer to one after the last character in
            the destination character sequence.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            stpncpy at 0x5e9c0 (ELF vaddr); 0x15e9c0 in Ghidra (image base 0x100000);
            callee memset at 0x18400 / 0x118400
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/stpncpy_armv8.v and
            ../lifted/memset_armv8.v (combined as stp_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q), X2 = dsize (n), SP = sp,
            X30 = raddr, X19 = x19, X29 = x29; memory mem.
   PRECONDITION (stp_pre sp mem d q n K), stated explicitly:
            - K = strnlen(src, n): bytes q..q+K-1 are nonzero, K <= n, and
              byte q+K is 0 when K < n;
            - n - K < 160 (the zero-fill memset avoids its DC ZVA path,
              which the lifter models as Nop; see memset_full_proof.v) and
              4096 <= d (memset's precondition);
            - 32 <= sp < 2^64; d+n+32 <= sp and q+n+32 <= sp, i.e. both
              buffers lie below stpncpy's own stack frame (sp-32..sp-1);
            - the destination d..d+n-1 does not overlap the source q..q+n-1
              (q+n <= d or d+n <= q).
            Justification: overlap is undefined behaviour (restrict); a
            destination overlapping stpncpy's own frame is not caller-owned
            memory; n - K < 160 is a limitation of the lift (DC ZVA / dczid_el0).
   Output:  If execution reaches the RET (0x15ea90), with
            F = mem with x29, raddr, x19 stored at sp-32, sp-24, sp-16
            (the saved frame, stp_frame) and M the final memory:
            X0 = d + K;
            M[d+i] = mem[q+i] for i < K (the non-NUL prefix is copied);
            M[d+i] = 0 for K <= i < n (NUL padding);
            M[a] = F[a] for every other address a (a < d or d+n <= a);
            SP = sp, X19 = x19, X29 = x29, X30 = raddr (stp_post).
            X20..X28 and Z8..Z15 are never written
            (stpncpy_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require stpncpy_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import memset_proof stpncpy_callees.
From Grok.proofs Require stpncpy_vcs.
Import ARM8Notations.
Open Scope N.

(* The last four invariant-set parameters (mm md cc mn) only describe the
   memset callee's family-0 invariants; the call site re-instantiates them
   with the actual call state (perform_call), so they are fixed to 0 here. *)
Theorem stpncpy_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x29 K t xs'
    (PRE0: stp_pre sp mem d q n K)
    (P1: stpncpy_armv8.stpncpy_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e9c0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr d q n x19 x29 K 0 0 0 0) (exits1 sp mem raddr d q n x19 x29 K 0 0 0 0) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  pose proof (MDL R_X2 64 eq_refl) as W2. rewrite X2 in W2. simpl in W2.
  assert (PP: stp_prog ⊆2 prog) by (apply stp_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=stp_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X29 START PRE0 W19 W29 W30 W0 W1 W2.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stp_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0 W1 W2. rename t1 into t.
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W29, W30, W0, W1, W2. clear WW.
  destruct_inv 64 PRE.
  - eapply stpncpy_vcs.stp_case_15e9c0; eassumption.
  - eapply stpncpy_vcs.stp_case_15e9ec; eassumption.
  - eapply stpncpy_vcs.stp_case_15ea0c; eassumption.
  - eapply stpncpy_vcs.stp_case_15ea38; eassumption.
  - eapply stpncpy_vcs.stp_case_15ea64; eassumption.
  - eapply stpncpy_vcs.stp_case_15ea78; eassumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorem: stpncpy and memset never write X20..X28 or Z8..Z15.     *)
Theorem stpncpy_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates stp_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
