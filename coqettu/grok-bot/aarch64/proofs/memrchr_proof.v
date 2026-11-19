(* memrchr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (src/string/memrchr.c)

   SEMANTICS
   ---------
   void *memrchr(const void *s, int c, size_t n): scans the n bytes at s
   backwards for the byte (unsigned char)c and returns a pointer to the
   last occurrence, or a null pointer if there is none.  musl's C:
     const unsigned char *s = m; c = (unsigned char)c;
     while (n--) if (s[n]==c) return s+n;   (as a void pointer)
     return 0;
   GCC vectorised the loop: when n > 14 and s+n is 16-byte aligned the
   binary first runs a NEON block search (0x15e85c..0x15e8e8: tbl, zip,
   cmeq, umaxp), then a scalar tail; otherwise it runs only the scalar
   byte loop at 0x15e918..0x15e940.

   SPECIFICATION (man 3 memrchr, Linux man-pages 6.9.1)
   ----------------------------------------------------
     The memrchr() function is like the memchr() function, except that it
     searches backward from the end of the n bytes pointed to by s instead
     of forward from the beginning.
     The memchr() and memrchr() functions return a pointer to the matching
     byte or NULL if the character does not occur in the given memory area.

   THEOREM AND PRECONDITIONS
   -------------------------
   memrchr_partial_correctness, scalar path only:
   - n <= 14 or (s + n) mod 16 <> 0: the NEON block path (0x15e85c) is
     proved unreachable under this precondition; it is not verified.
   - 0 < s and s + n < 2^64: the loop compares the cursor against s - 1,
     so the object must not start at address 0 or wrap the address space.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memrchr at 0x5e83c (ELF vaddr); 0x15e83c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/memrchr_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = p, X1 = c, X2 = n; X30 = return address raddr; SP = sp;
            mem = memory on entry.  c8 = c mod 2^8.
   Output:  At the RET (0x15e948), either X0 = p + k for some k < n with
            mem[p+k] = c8 and no byte equal to c8 in [p+k+1, p+n), or X0 = 0
            and no byte equal to c8 in [p, p+n).  Memory, SP and X30 are
            unchanged; the AAPCS64 callee-saved registers are unchanged
            (memrchr_preserves_callee_saved).
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memrchr_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCov.
From Grok.proofs Require Import memrchr_defs memrchr_lib.
Import ARM8Notations.
Open Scope N.

Theorem memrchr_welltyped: welltyped_prog arm8typctx memrchr_armv8.
Proof. Picinae_typecheck. Qed.

Theorem memrchr_nwc: ∀ s2 s1, memrchr_armv8 s1 = memrchr_armv8 s2.
Proof. reflexivity. Qed.

Theorem memrchr_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memrchr_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memrchr_preserves_x30:
  forall_endstates memrchr_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem memrchr_partial_correctness: ∀ prog s sp mem raddr x19 x29 p c n t xs'
    (PROG: memrchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e83c, s))
    (MDL: models arm8typctx s) (HPRE: mrc_pre sp mem raddr x19 x29 p c n s),
  satisfies_all prog (memrchr_invs 0 sp mem raddr x19 x29 p c n) (memrchr_exits 0 sp mem raddr x19 x29 p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memrchr_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memrchr_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memrchr_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  (* the NEON block invariant (False) at 0x15e85c is discharged by destruct_inv *)
  - (* entry 0x15e83c *)
    destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & PP & PN & NEON & X19 & X29).
    repeat grok_step; try match goal with H: models _ _ |- _ => clear H end; bools_to_props_mr.
    all: first [ solve [mrc_neon NEON] | solve [mrc_enter n] ].
  - (* scalar loop 0x15e924 *)
    destruct PRE as (k & KN & X2 & X4 & X1 & PP & PN & NM & MEM & SP & X30 & X19 & X29).
    repeat grok_step; try match goal with H: models _ _ |- _ => clear H end; bools_to_props_mr.
    all: first [ solve [mrc_null k NM BC] | solve [mrc_found k NM BC BC0] | solve [mrc_next k NM BC BC0] ].
Qed.
