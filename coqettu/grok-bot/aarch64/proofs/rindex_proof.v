(* rindex -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (tail call to strrchr)

   SEMANTICS
   ---------
   musl's src/legacy/rindex.c:
       char *rindex(const char *s, int c) { return strrchr(s, c); }
   compiled to a single instruction at 0x15e94c: b 0x15f228 (strrchr).  The
   proof reuses strrchr_partial_correctness (proofs/strrchr_proof.v, which
   covers strrchr, strlen and memrchr) through the generic tail-call lemma
   tailcall_satisfies_all of lib/GrokTail.v.

   SPECIFICATION (man 3 rindex, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            [[deprecated]] char *rindex(const char *s, int c);

     DESCRIPTION
            rindex() is identical to strrchr(3).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            rindex at 0x5e94c (ELF vaddr); 0x15e94c in Ghidra (image base 0x100000);
            target strrchr at 0x5f228 / 0x15f228
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/rindex_armv8.v,
            ../lifted/strrchr_armv8.v, ../lifted/memrchr_armv8.v and
            ../lifted/strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = c, SP = sp, X30 = raddr, X19 = x19, X29 = x29,
            memory mem; the program contains rindex, strrchr, memrchr and
            strlen.  Preconditions exactly those of strrchr_partial_correctness
            (k = strlen in the framed memory, n = k + 1, memrchr scalar path).
   Output:  Exactly strrchr's invariant set and postcondition (invs1/exits1
            of strrchr_defs.v): at memrchr's RET, X0 points to the last
            occurrence of c mod 2^8 in [p, p+n), or is 0 if there is none;
            SP, X19, X29, X30 restored.  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require rindex_armv8 strrchr_armv8 memrchr_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import strrchr_defs strrchr_proof.
Import ARM8Notations.
Open Scope N.

Theorem rindex_partial_correctness:
  ∀ prog s sp mem raddr x19 x29 p c n k t xs'
    (P3: rindex_armv8.rindex_armv8 ⊆2 prog)
    (P2: strrchr_armv8.strrchr_armv8 ⊆2 prog) (P1: memrchr_armv8.memrchr_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e94c, s)) (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p) (X1: s R_X1 = c)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29)
    (NF: nilfree (rr_frame sp mem raddr x19 x29 c) p k) (NZ: rr_frame sp mem raddr x19 x29 c Ⓑ[p + k] = 0)
    (KN: n = k + 1) (PP: 0 < p) (PN: p + n < 2^64) (NEON: n <= 14 \/ (p + n) mod 16 <> 0),
  satisfies_all prog (invs1 sp mem raddr x19 x29 p c n) (exits1 sp mem raddr x19 x29 p c n) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog (invs1 sp mem raddr x19 x29 p c n) (exits1 sp mem raddr x19 x29 p c n))
    with (a0 := 0x15e94c) (a1 := 0x15f228)
         (P := fun s => models arm8typctx s /\ s R_SP = sp /\ s V_MEM64 = mem /\ s R_X30 = raddr /\
                        s R_X0 = p /\ s R_X1 = c /\ s R_X19 = x19 /\ s R_X29 = x29) (s := s).
  - intros [[a|i] s1] t1 t2; reflexivity.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro s1. apply P3. reflexivity.
  - intros s1 s2 E (M & H1 & H2 & H3 & H4 & H5 & H6 & H7). rewrite <- !E.
    split; [|repeat split; assumption]. intros v w CV. rewrite <- E. exact (M v w CV).
  - intros s1 t1 xs1 START (M & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    eapply strrchr_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat split; assumption.
Qed.
