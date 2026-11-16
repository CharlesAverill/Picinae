(* stpcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/string/stpcpy.c (word-at-a-time when src and dst have equal
   alignment mod 8, HASZERO(x) = (x - ONES) & ~x & HIGHS):
       char *__stpcpy(char *restrict d, const char *restrict s) {
           if ((uintptr_t)s % ALIGN == (uintptr_t)d % ALIGN) {
               for (; (uintptr_t)s % ALIGN; s++, d++)
                   if (!( *d = *s )) return d;
               wd=(void * )d; ws=(const void * )s;
               for (; !HASZERO( *ws ); *wd++ = *ws++);
               d=(void * )wd; s=(const void * )ws;
           }
           for (; ( *d = *s ); s++, d++);
           return d;
       }
       weak_alias(__stpcpy, stpcpy);

   SPECIFICATION (man 3 stpcpy, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            char *stpcpy(char *restrict dst, const char *restrict src);
     DESCRIPTION
            These functions copy the string pointed to by src, into a string
            at the buffer pointed to by dst.  The programmer is responsible
            for allocating a destination buffer large enough, that is,
            strlen(src) + 1.
            stpcpy() copies the terminating null byte as well.
     RETURN VALUE
            stpcpy() returns a pointer to the terminating null byte in the
            copied string.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            stpcpy at 0x5e950 (ELF vaddr); 0x15e950 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/stpcpy_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q); X30 = return address.
   Output:  If execution reaches the RET (0x15e9bc) there is a k such that
            bnz mem d q k (each of the first k source bytes read was nonzero),
            the source byte read at q+k is 0, memory = bcp mem d q (k+1), and
            X0 = d + k mod 2^64 (pointer to the copied terminator).
            bcp (lib/GrokStr.v) is the sequential byte-by-byte copy
            dst[i] := src[i] for i = 0..k, each read seeing earlier writes,
            so no non-overlap precondition is needed; for non-overlapping
            buffers it is exactly the C semantics.  The 8-byte word path is
            shown equal to 8 sequential byte copies when
            (src - dst) mod 8 = 0, which the code tests.
            SP and X30 are unchanged.  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import stpcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.lib Require Import GrokStr.
Import ARM8Notations.
Open Scope N.

Theorem stpcpy_welltyped: welltyped_prog arm8typctx stpcpy_armv8.
Proof. Picinae_typecheck. Qed.


Section Invariants.
  Variables (sp mem raddr d q : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e950 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e95c => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e990 => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X4 = K8 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e9ac => Inv 0 (∃ k, s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e9bc => Post 0 (∃ k, bnz mem d q k /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = 0 /\
                          s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\
                          s R_X0 = (d + k) mod 2^64 /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition stpcpy_exits := make_exits 0 stpcpy_armv8 invs.
  Definition stpcpy_invs := make_invs 0 stpcpy_armv8 invs.
End Invariants.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.
Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Theorem stpcpy_partial_correctness:
  ∀ prog s sp mem raddr d q t xs'
    (PROG: stpcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e950, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q),
  satisfies_all prog (stpcpy_invs sp mem raddr d q) (stpcpy_exits sp mem raddr d q) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=stpcpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold stpcpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stpcpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as BD. pose proof (MDL1 R_X1 64 eq_refl) as BQ.
    rewrite X0 in BD. rewrite X1 in BQ.
    repeat arm8_step.
    + exists 0. apply N.eqb_eq in BC. split.
      * transitivity (msub 64 q d mod 2^3).
        rewrite msub_mod_pow2. reflexivity. apply xor_mod8. exact BC.
      * repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
        intros i I. lia.
    + exists 0.
      repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
      intros i I. lia.
  - destruct PRE as (k & AL & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    + exists k. split. al3. split. reflexivity. repeat split; assumption.
    + exists k. apply N.eqb_eq in BC0. repeat split; try assumption. rewrite bcp_succ. reflexivity.
    + exists (k+1). apply N.eqb_neq in BC0. split. al3. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
  - destruct PRE as (k & AL & X4 & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    + exists (k+8). apply N.eqb_eq in BC. split. al3. split. reflexivity. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply (bnz_word mem d q k _ AL eq_refl); [|exact NZ].
        apply haszero_none'; [apply getmem_bound | exact BC].
      * rewrite bcp_word8 by exact AL. reflexivity.
    + exists k. repeat split; assumption.
  - destruct PRE as (k & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k)) as B;
         change (2^(1*8)) with (2^8) in B;
         destruct (byte_test _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
    + exists k. repeat split; try assumption. rewrite bcp_succ. reflexivity.
Qed.
