(* strtok, short separator-set path -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C
   (calls strspn and strcspn; strcspn calls __strchrnul, which may call strlen)

   SEMANTICS
   ---------
   musl's src/string/strtok.c:
       char *strtok(char *restrict s, const char *restrict sep) {
           static char *p;
           if (!s && !(s = p)) return NULL;
           s += strspn(s, sep);
           if (!*s) return p = 0;
           p = s + strcspn(s, sep);
           if ( *p) *p++ = 0;
           else p = 0;
           return s;
       }
   compiled as: 64-byte frame (stp x29,x30,[sp,#-64]!; x19,x20 at sp-48/-40,
   x21 at sp-32), x21 = 0x1c2000 (adrp) so the static p lives at
   G = x21+0x5e0 = 0x1c25e0; cbz x0 -> ldr x19,[G], cbnz x19 -> join 0x15f7e0,
   else return 0; join: bl strspn (0x15f2e8); ldrb w0,[x19,x0]; if zero
   str xzr,[G] and return 0; else spill s+K at sp-8, bl strcspn (0x15ecf0),
   reload, ldrb w3,[x2,x0]; if zero str xzr,[G]; else str (end+1),[G] and
   strb wzr,[end]; return s+K.  Both callee proofs (strspn_proof.v,
   strcspn_proof.v) are reused through lib/GrokCall.v
   (satisfies_all_transfer), carrying the caller's X19/X20/X21/X29 across the
   calls with lib/GrokKeep.v (keepl).  This file covers separator sets with
   strlen(sep) < 2, for which strcspn takes its __strchrnul path; the
   strcspn_short proof (strcspn_short_proof.v) is reused, and strspn's
   invariant family is renumbered 0 -> 3 inside strtok's family (ids: strtok 4,
   strspn 3, strcspn 2, __strchrnul 1, strlen 0).  strtok_proof.v covers
   strlen(sep) >= 2; together they cover every separator set.

   SPECIFICATION (man 3 strtok, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            char *strtok(char *restrict str, const char *restrict delim);
     DESCRIPTION
            The strtok() function breaks a string into a sequence of zero or
            more nonempty tokens.  On the first call to strtok(), the string to
            be parsed should be specified in str.  In each subsequent call that
            should parse the same string, str must be NULL.
            The delim argument specifies a set of bytes that delimit the tokens
            in the parsed string.
            Each call to strtok() returns a pointer to a null-terminated string
            containing the next token.  This string does not include the
            delimiting byte.  If no more tokens are found, strtok() returns NULL.
            The end of each token is found by scanning forward until either the
            next delimiter byte is found or until the terminating null byte
            ('\0') is encountered.  If a delimiter byte is found, it is
            overwritten with a null byte to terminate the current token, and
            strtok() saves a pointer to the following byte; that pointer will
            be used as the starting point when searching for the next token.
            A sequence of two or more contiguous delimiter bytes in the parsed
            string is considered to be a single delimiter.  Delimiter bytes at
            the start or end of the string are ignored.
     RETURN VALUE
            The strtok() function returns a pointer to the next token, or NULL
            if there are no more tokens.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strtok at 0x5f7c4 (ELF vaddr); 0x15f7c4 in Ghidra (image base 0x100000);
            callees strspn 0x5f2e8 / 0x15f2e8, strcspn 0x5ecf0 / 0x15ecf0,
            __strchrnul 0x5ebf4 / 0x15ebf4, strlen 0x5efa8 / 0x15efa8;
            static p at 0xc25e0 / 0x1c25e0
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strtok_armv8.v,
            ../lifted/strspn_armv8.v, ../lifted/strcspn_armv8.v,
            ../lifted/strchrnul_armv8.v and ../lifted/strlen_armv8.v
            (combined as tks_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (s0), X1 = sep (c), SP = sp, X30 = raddr, X19 = x19,
            X20 = x20, X21 = x21, X29 = x29; memory mem; G = 0x1c25e0 (static p).
   PRECONDITION (tks_pre sp mem s0 p c Ks Lc), stated explicitly:
            - p is the string actually scanned: s0 <> 0 and p = s0, or
              s0 = 0 and p = mem Ⓠ[G];
            - G+184 <= sp < 2^64;
            - p = 0, or: Ks = strlen(p), Lc = strlen(c), Lc < 2, the two
              16-byte rodata words read by strspn's one-byte fast path
              (0x19e6b0, 0x19e6c0) are zero (as in the binary), and
              p+Ks+177 <= sp, c+Lc+177 <= sp (strings below the stack frames).
   Output:  At the RET 0x15f834 (tks_post): SP = sp, X19 = x19, X20 = x20,
            X21 = x21, X29 = x29, X30 = raddr, and, with M the final memory and
            "M agrees with N" meaning M[a] = N[a] for every a outside
            sp-176..sp-1 (tks_out):
            - p = 0: X0 = 0 and M agrees with mem;
            - else for K1 <= Ks with every p[i], i < K1, in c[0..Lc)
              (K1 = strspn(p, c)):
              - K1 = Ks (only delimiters left): X0 = 0, M agrees with mem[Ⓠ G := 0];
              - K1 < Ks, p[K1] not in c: X0 = p+K1, and for K2 with
                K1+K2 <= Ks and no p[K1+i], i < K2, in c (K2 = strcspn(p+K1, c)):
                - K1+K2 = Ks: M agrees with mem[Ⓠ G := 0];
                - K1+K2 < Ks, p[K1+K2] in c: M agrees with
                  mem[Ⓠ G := p+K1+K2+1][Ⓑ p+K1+K2 := 0].
            X22..X28 and Z8..Z15 are never written
            (strtok_short_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall GrokKeep.
From Grok.proofs Require Import strtok_defs strtok_callees strtok_join.
From Grok.proofs Require strcspn_defs strspn_defs strspn_proof.
From Grok.proofs Require Import strcspn_short_defs strcspn_short_proof.
From Grok.proofs Require Import strtok_short_defs strtok_short_callees strtok_short_join.
Import ARM8Notations.
Open Scope N.

Theorem strtok_short_partial_correctness:
  ∀ prog s sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 t xs'
    (PRE0: tks_pre sp mem s0 p c Ks Lc)
    (P3: strtok_armv8.strtok_armv8 ⊆2 prog) (P2: strspn_armv8.strspn_armv8 ⊆2 prog)
    (P1: strcspn_armv8.strcspn_armv8 ⊆2 prog) (PC: strchrnul_armv8.strchrnul_armv8 ⊆2 prog)
    (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f7c4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = s0) (X1: s R_X1 = c)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29),
  satisfies_all prog (tks_invs4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0)
                     (tks_exits4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  assert (PP: tks_prog ⊆2 prog) by (apply tks_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=tks_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold tks_invs4, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 START PRE0 W19 W20 W21 W29 W30 W0 W1.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply tks_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W29 W30 W0 W1. rename t1 into t.
  destruct_inv 64 PRE.
  - eapply tks_case_entry; eassumption.
  - eapply tks_case_join; eassumption.
Qed.

Theorem strtok_short_preserves_other_callee_saved:
  ∀ r, In r (R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates tks_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
