(* wcstok -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcsspn and wcscspn)

   SEMANTICS
   ---------
   musl's src/string/wcstok.c:
       if (!s && !(s = *p)) return NULL;
       s += wcsspn(s, sep);
       if (!*s) return *p = 0;
       *p = s + wcscspn(s, sep);
       if ( **p) *( *p)++ = 0;      (spaces added inside the parentheses)
       else *p = 0;
       return s;
   The binary pushes a 48-byte frame (X29, X30 at sp-48/sp-40, X19, X20 at
   sp-32/sp-24, X21, X22 at sp-16/sp-8), keeps s in X19, sep in X20, p in
   X21 and the token start in X22, and calls wcsspn (0x15fe6c) and wcscspn
   (0x15fb44).  wcsspn and wcscspn both call wcschr, whose loop head 0x15fae0
   has a different invariant in each proof; wcscspn may also tail-call
   wcslen.  Both proofs (wcsspn_proof.v, wcscspn_proof.v) are reused whole at
   level 1:
     lib/GrokExits.v changes the exit predicate,
     lib/GrokKeep.v carries X22 across wcscspn,
     lib/GrokWeaken.v moves the invariants into the wcstok family (a
       disjunction at 0x15fae0),
     lib/GrokCall2.v transfers the proof to the whole program.
   A phase parameter in the family (0 for the wcsspn call, 1 for wcscspn)
   rules out the other callee's return points as exits of a call.

   SPECIFICATION (man 3 wcstok, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcstok(wchar_t *restrict wcs, const wchar_t *restrict delim,
                            wchar_t **restrict ptr);

     DESCRIPTION
            The search starts at wcs, if wcs is not NULL, or at *ptr, if wcs
            is NULL.  First, any delimiter wide-characters are skipped, that
            is, the pointer is advanced beyond any wide-characters which occur
            in delim.  If the end of the wide-character string is now reached,
            wcstok() returns NULL, to indicate that no tokens were found, and
            stores an appropriate value in *ptr, so that subsequent calls to
            wcstok() will continue to return NULL.  Otherwise, the wcstok()
            function recognizes the beginning of a token and returns a pointer
            to it, but before doing that, it zero-terminates the token by
            replacing the next wide-character which occurs in delim with a
            null wide character (L'\0'), and it updates *ptr so that
            subsequent calls will continue searching after the end of
            recognized token.

     RETURN VALUE
            The wcstok() function returns a pointer to the next token, or
            NULL if no further token was found.

   THEOREM AND PRECONDITIONS
   -------------------------
   wcstok_partial_correctness, with s = wt_str mem s0 p (s0 itself, or the
   saved pointer mem[p] when s0 = 0) and wt_pre sp mem s0 sep p Ls Lc:
   - 96 <= sp < 2^64 and the 8 bytes at p lie below sp - 48 (below the frame);
   - if s <> 0: s has Ls nonzero wide characters then L'\0' (Ls < 2^61), sep
     has Lc nonzero wide characters then L'\0', 0 < sep, and both strings
     end at or below sp - 96 (below the frames of wcstok and its callees).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcstok at 0x6013c (ELF vaddr); 0x16013c in Ghidra (image base 0x100000);
            callees wcsspn 0x15fe6c, wcscspn 0x15fb44, wcschr 0x15fab4, wcslen 0x15fc18.
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcstok_armv8.v,
            wcsspn_armv8.v, wcscspn_armv8.v, wcschr_armv8.v, wcslen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s0 (wcs), X1 = sep (delim), X2 = p (ptr); X30 = raddr,
            SP = sp, X19..X22 = x19..x22, X29 = x29; mem = memory on entry.
   Output:  At wcstok's RET (0x1601a8; wt_post at level 2): SP = sp,
            X30 = raddr, X19..X22 = x19..x22, X29 = x29, and, with M1 the
            memory after the frame is pushed (wt_M1), W1 = M1 plus wcsspn's
            frame (wt_W1), and W = W1 or W1 plus wcscspn's frame (wt_W2):
            (1) s = 0: X0 = 0, memory M1 (nothing stored at p); or
            (2) the first k0 <= Ls characters of s are in sep (spn) and
                s[k0] = 0: X0 = 0, memory W1 with *p := 0; or
            (3) s[0..k0) are in sep, s[k0] <> 0 is not in sep, the j
                characters from s + 4k0 are nonzero and not in sep (cspn),
                k0 + j <= Ls, X0 = s + 4k0, and either s[k0+j] = 0 and memory
                is W with *p := 0, or s[k0+j] is in sep and memory is W with
                s[k0+j] := L'\0' then *p := s + 4(k0+j) + 4.
            Facts about s and sep are stated in the caller's memory mem.
            X23..X28 and Z8..Z15 are never written by wcstok, wcsspn,
            wcscspn, wcschr or wcslen (wcstok_preserves_other_callee_saved).
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcstok_armv8 wcsspn_armv8 wcscspn_armv8 wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib wcstok_vc_entry.
Import ARM8Notations.
Open Scope N.

Theorem wcstok_partial_correctness:
  ∀ prog st sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc t xs'
    (P4: wcstok_armv8.wcstok_armv8 ⊆2 prog) (P3: wcsspn_armv8.wcsspn_armv8 ⊆2 prog)
    (P2: wcscspn_armv8.wcscspn_armv8 ⊆2 prog) (P1: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x16013c, st)) (MDL: models arm8typctx st)
    (SP: st R_SP = sp) (MEM: st V_MEM64 = mem) (X30: st R_X30 = raddr)
    (X0: st R_X0 = s0) (X1: st R_X1 = sep) (X2: st R_X2 = p)
    (X19: st R_X19 = x19) (X20: st R_X20 = x20) (X21: st R_X21 = x21) (X22: st R_X22 = x22) (X29: st R_X29 = x29)
    (PRE0: wt_pre sp mem s0 sep p Ls Lc),
  satisfies_all prog (wt_invs2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)
                     (wt_exits2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X22 64 eq_refl) as W22. rewrite X22 in W22. simpl in W22.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  eapply satisfies_all_pmono with (p1:=wt_prog).
    apply wt_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wt_invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X21 X22 X29 PRE0 W19 W20 W21 W22 W29 W30 START.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wt_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W22 W29 W30. rename t1 into t.
  destruct_inv 64 PRE.
  eapply (wt_case_entry sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc); first [ exact PRE | sassumption | assumption ].
Qed.
