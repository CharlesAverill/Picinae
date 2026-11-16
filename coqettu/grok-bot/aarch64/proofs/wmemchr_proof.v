(* wmemchr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/wmemchr.c:
       for (; n && *s != c; n--, s++);
       return n ? s : 0;         [s cast back to a non-const pointer]
   compiled to a single loop: cbz x2 (return 0); ldr w3,[x0]; sub x2,x2,#1;
   cmp w3,w1; b.ne (x0 += 4, repeat); else return x0.  wchar_t is a 32-bit
   int on aarch64, compared for equality on the low 32 bits.
   NOTE: Ghidra split this function at the loop head; the lift used here is
   Ghidra's FUN_001601d8, which covers 0x1601d0..0x1601f4 (all of wmemchr).

   SPECIFICATION (man 3 wmemchr, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wmemchr(const wchar_t s[.n], wchar_t c, size_t n);

     DESCRIPTION
            The wmemchr() function is the wide-character equivalent of the
            memchr(3) function.  It searches the n wide characters starting at
            s for the first occurrence of the wide character c.

     RETURN VALUE
            The wmemchr() function returns a pointer to the first occurrence of
            c among the n wide characters starting at s, or NULL if c does not
            occur among these.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wmemchr at 0x601d0 (ELF vaddr); 0x1601d0 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wmemchr_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, W1 = c (c32 = c mod 2^32), X2 = n; X30 = return address;
            m = memory on entry.
   Output:  If execution reaches the RET (0x1601f4), then either
              - there is k < n with X0 = s + 4k (mod 2^64), the 32-bit words
                m[s+4i] differ from c32 for all i < k, and m[s+4k] = c32, or
              - X0 = 0 (NULL) and m[s+4i] <> c32 for all i < n.
            (Words are read little-endian; addresses wrap modulo 2^64.)
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemchr_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem wmemchr_nwc: ∀ s2 s1, wmemchr_armv8 s1 = wmemchr_armv8 s2.
Proof. reflexivity. Qed.

Theorem wmemchr_welltyped: welltyped_prog arm8typctx wmemchr_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemchr_preserves_memory:
  forall_endstates wmemchr_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wmemchr_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wmemchr_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wmemchr_preserves_x30:
  forall_endstates wmemchr_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

(* No wide character among the first k at p equals c. *)
Definition wnomatch (m:memory) (p:addr) (c:N) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ c.

Lemma wnomatch_0: ∀ m p c, wnomatch m p c 0.
Proof. unfold wnomatch. intros. lia. Qed.

Lemma wnomatch_succ: ∀ m p c k, wnomatch m p c k -> m Ⓓ[p + 4*k] ≠ c -> wnomatch m p c (k+1).
Proof.
  unfold wnomatch. intros m p c k NM B i I.
  destruct (N.lt_ge_cases i k). apply NM; assumption. replace i with k by lia. exact B.
Qed.

Section Invariants.
  Variables (sp mem raddr p c n : N).
  Definition c32 := c mod 2^32.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x1601d0 => Inv 0 (s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1601d8 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X2 = n - k /\ s R_X1 = c /\
                         wnomatch mem p c32 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1601f4 => Post 0 (((∃ k, k < n /\ s R_X0 = p ⊕ 4*k /\ wnomatch mem p c32 k /\ mem Ⓓ[p + 4*k] = c32) \/
                           (s R_X0 = 0 /\ wnomatch mem p c32 n)) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wmemchr_exits := make_exits 0 wmemchr_armv8 invs.
  Definition wmemchr_invs := make_invs 0 wmemchr_armv8 invs.
End Invariants.


Theorem wmemchr_partial_correctness:
  ∀ prog s sp mem raddr p c n t xs'
    (PROG: wmemchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1601d0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X2: s R_X2 = n),
  satisfies_all prog (wmemchr_invs sp mem raddr p c n) (wmemchr_exits sp mem raddr p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemchr_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wmemchr_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemchr_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X2 in N64. simpl in P64, N64.
    repeat arm8_step.
    exists 0.
    repeat split; try assumption; try lia. apply wnomatch_0.
  - destruct PRE as (k & N64 & KLE & X0 & X2 & X1 & NM & MEM & SP & X30).
    pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
    repeat arm8_step.
    + apply N.eqb_eq in BC. split; [|repeat split; assumption].
      right. split. reflexivity. replace n with k by lia. exact NM.
    + apply N.eqb_eq in BC0. apply N.eqb_neq in BC. split; [|repeat split; assumption].
      left. exists k. repeat split; try assumption; try exact BC0; lia.
    + apply N.eqb_neq in BC0, BC. exists (k+1).
      repeat split; try assumption; try lia.
      all: first [ (f_equal; lia) | (rewrite msub_small by lia; lia) | (apply wnomatch_succ; assumption) ].
Qed.
