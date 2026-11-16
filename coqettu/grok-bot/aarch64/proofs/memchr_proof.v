(* memchr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (word-at-a-time)

   SEMANTICS
   ---------
   musl's src/string/memchr.c: c is reduced to an unsigned char; the
   function scans byte-wise while s is not 8-byte aligned, then (if the
   aligned byte is not c) a word at a time over the 8-byte words that lie
   wholly inside the n bytes, using HASZERO(w XOR splat(c)) with
       HASZERO(x) = (x - ONES) AND NOT x AND HIGHS,
       ONES = 0x0101..01, HIGHS = 0x8080..80, splat(c) = c * ONES,
   and finally byte-wise over the remaining bytes (starting at the first
   word whose test fired, if any).  It returns a pointer to the first byte
   equal to c, or NULL (0) if none of the n bytes equals c.

   In the binary the cursor is X3 (byte/word loops) and X0 (tail loop);
   X7 = s+n, X0 = s + (n AND NOT 7) bounds the word loop, X6 = splat(c),
   X8 = 0xfefefefefefefeff (= -ONES).  The proof relies on
   GrokBits.hasbyte_test_zero: if the test is zero, none of the 8 bytes of
   the word equals c.

   SPECIFICATION (man 3 memchr, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            void *memchr(const void s[.n], int c, size_t n);

     DESCRIPTION
            The memchr() function scans the initial n bytes of the memory area
            pointed to by s for the first instance of c.  Both c and the bytes
            of the memory area pointed to by s are interpreted as unsigned char.

     RETURN VALUE
            The memchr() and memrchr() functions return a pointer to the
            matching byte or NULL if the character does not occur in the given
            memory area.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memchr at 0x5e1ec (ELF vaddr); 0x15e1ec in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/memchr_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = c (only its low 8 bits matter, c8 = c mod 2^8),
            X2 = n; X30 = return address; m = memory on entry.
   Output:  If execution reaches the RET (0x15e2a4), then either
              - there is k < n with X0 = s+k (mod 2^64), m[s+i] <> c8 for all
                i < k, and m[s+k] = c8 (the first match), or
              - X0 = 0 (NULL) and m[s+i] <> c8 for all i < n.
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.  Addresses wrap modulo 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memchr_armv8.
From Grok.lib Require Import GrokCommon GrokBits.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem memchr_nwc: ∀ s2 s1, memchr_armv8 s1 = memchr_armv8 s2.
Proof. reflexivity. Qed.

Theorem memchr_welltyped: welltyped_prog arm8typctx memchr_armv8.
Proof. Picinae_typecheck. Qed.

Theorem memchr_preserves_memory:
  forall_endstates memchr_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem memchr_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memchr_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memchr_preserves_x30:
  forall_endstates memchr_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

(* No byte among the first k at p equals c. *)
Definition nomatch (m:memory) (p:addr) (c:N) (k:N) := ∀ i, i < k -> m Ⓑ[p + i] ≠ c.

Section Invariants.
  Variables (sp mem raddr p c n : N).
  Definition c8 := c mod 2^8.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e1ec => Inv 0 (s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e200 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X3 = p ⊕ k /\ s R_X2 = n - k /\ s R_X1 = c8 /\
                         nomatch mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e218 => Inv 0 (∃ k, n < 2^64 /\ k < n /\ s R_X3 = p ⊕ k /\ s R_X2 = n - k /\ s R_X1 = c8 /\
                         nomatch mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e258 => Inv 0 (∃ k e, n < 2^64 /\ k <= e /\ e <= n /\ (e - k) mod 8 = 0 /\
                         s R_X3 = p ⊕ k /\ s R_X0 = p ⊕ e /\ s R_X7 = p ⊕ n /\
                         s R_X6 = c8 * 0x0101010101010101 /\ s R_X8 = 0xfefefefefefefeff /\
                         s R_X1 = c8 /\ nomatch mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e288 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ k /\ s R_X2 = n - k /\ s R_X1 = c8 /\
                         nomatch mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e2a4 => Post 0 (((∃ k, k < n /\ s R_X0 = p ⊕ k /\ nomatch mem p c8 k /\ mem Ⓑ[p + k] = c8) \/
                           (s R_X0 = 0 /\ nomatch mem p c8 n)) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition memchr_exits := make_exits 0 memchr_armv8 invs.
  Definition memchr_invs := make_invs 0 memchr_armv8 invs.
End Invariants.


Lemma nomatch_0: ∀ m p c, nomatch m p c 0.
Proof. unfold nomatch. intros. lia. Qed.

Lemma nomatch_succ: ∀ m p c k, nomatch m p c k -> m Ⓑ[p + k] ≠ c -> nomatch m p c (k+1).
Proof.
  unfold nomatch. intros m p c k NM B i I.
  destruct (N.lt_ge_cases i k). apply NM; assumption. replace i with k by lia. exact B.
Qed.

Lemma nomatch_8: ∀ m p c k, nomatch m p c k -> (∀ j, j < 8 -> m Ⓑ[p + k + j] ≠ c) -> nomatch m p c (k+8).
Proof.
  unfold nomatch. intros m p c k NM B i I.
  destruct (N.lt_ge_cases i k). apply NM; assumption.
  replace (p + i) with (p + k + (i - k)) by lia. apply B. lia.
Qed.

Lemma land_mask8: ∀ x, x < 2^64 -> x .& 0xfffffffffffffff8 = 8 * (x / 8).
Proof.
  intros x X.
  change 0xfffffffffffffff8 with (N.lxor (N.ones 3) (N.ones 64)).
  transitivity (N.ldiff x (N.ones 3)).
  2: rewrite N.ldiff_ones_r, N.shiftl_mul_pow2, N.shiftr_div_pow2; apply N.mul_comm.
  apply N.bits_inj. intro b.
  rewrite N.land_spec, N.lxor_spec, N.ldiff_spec.
  destruct (N.lt_ge_cases b 64).
  - rewrite (N.ones_spec_low 64) by assumption. destruct (N.testbit (N.ones 3) b); reflexivity.
  - rewrite (bound_hibits_zero 64 x b X H). reflexivity.
Qed.

Lemma c8_lt: ∀ c, c8 c < 2^8.
Proof. intros. apply N.mod_lt. discriminate. Qed.

Lemma c8_lt31: ∀ c, c8 c < 2^31.
Proof. intros. eapply N.lt_le_trans. apply c8_lt. discriminate. Qed.

Lemma splat_lt: ∀ c, c < 2^8 -> c * 0x0101010101010101 < 2^64.
Proof. intros c H. change (2^8) with 256 in H. change (2^64) with 18446744073709551616. lia. Qed.

Lemma mod_small64: ∀ x, x < 2^64 -> x mod 2^64 = x.
Proof. intros. apply N.mod_small. assumption. Qed.

Lemma step8: ∀ k e, k <= e -> (e - k) mod 8 = 0 -> k <> e -> k + 8 <= e /\ (e - (k + 8)) mod 8 = 0.
Proof.
  intros k e KE M NE. pose proof (N.div_mod (e - k) 8 ltac:(discriminate)) as D.
  rewrite M, N.add_0_r in D.
  assert (Q: 1 <= (e - k) / 8) by lia.
  split. lia.
  replace (e - (k + 8)) with (((e - k) / 8 - 1) * 8) by lia. apply N.Div0.mod_mul.
Qed.

Ltac norm_bc := repeat match goal with
  | H: negb (_ =? _) = true |- _ => apply Bool.negb_true_iff, N.eqb_neq in H
  | H: negb (_ =? _) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H
  | H: (_ mod 8 =? 0) = _ |- _ => clear H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Ltac fin := first
  [ reflexivity | assumption | lia
  | apply nomatch_0
  | (apply nomatch_succ; assumption)
  | (apply nomatch_8; assumption)
  | (match goal with |- nomatch _ _ _ ?n => match goal with H: nomatch _ _ _ ?k |- _ =>
       replace n with k by lia; exact H end end)
  | (f_equal; lia)
  | (rewrite msub_small by lia; lia)
  | (rewrite land_mask8 by lia; f_equal; lia)
  | (rewrite N.shiftr_0_r; match goal with H: c8 ?c mod 2^32 = c8 ?c |- _ => rewrite H end;
     rewrite scast_small32 by apply c8_lt31; apply mod_small64, splat_lt, c8_lt)
  | (match goal with |- (?k + 8 * ?q - ?k) mod 8 = 0 =>
       replace (k + 8 * q - k) with (q * 8) by lia; apply N.Div0.mod_mul end)
  ].
Ltac fin_all := repeat split; fin.
Ltac post_or k := split; [ first [ left; exists k; solve [fin_all] | right; solve [fin_all] ] | solve [fin_all] ].


Theorem memchr_partial_correctness:
  ∀ prog s sp mem raddr p c n t xs'
    (PROG: memchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e1ec, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X2: s R_X2 = n),
  satisfies_all prog (memchr_invs sp mem raddr p c n) (memchr_exits sp mem raddr p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memchr_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memchr_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memchr_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  assert (C8 := c8_lt c).
  assert (C8' : c8 c mod 2^32 = c8 c) by (apply N.mod_small; change (2^32) with (2^8 * 2^24); lia).
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X2 in N64. simpl in P64, N64.
    repeat arm8_step.
    exists 0. rewrite N.add_0_r, N.sub_0_r, mod_small64 by assumption.
    repeat split; try assumption; try lia. apply nomatch_0.
  - (* 0x15e200: byte-alignment loop *)
    destruct PRE as (k & N64 & KLE & X3 & X2 & X1 & NM & MEM & SP & X30).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ post_or k
               | exists k; solve [fin_all]
               | exists (k+1); solve [fin_all] ].
  - (* 0x15e218: first aligned byte check, then set up word loop *)
    destruct PRE as (k & N64 & KLT & X3 & X2 & X1 & NM & MEM & SP & X30).
    pose proof (N.mul_div_le (n - k) 8 ltac:(discriminate)).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ exists k; solve [fin_all]
               | exists k, (k + 8 * ((n - k) / 8)); solve [fin_all] ].
  - (* 0x15e258: word loop *)
    destruct PRE as (k & e & N64 & KE & EN & KE8 & X3 & X0 & X7 & X6 & X8 & X1 & NM & MEM & SP & X30).
    repeat arm8_step; rewrite ?C8' in *;
    try match goal with H: (msub 64 _ _ .& _ .& _ =? 0) = true |- _ =>
          pose proof (hasbyte_test_zero _ _ _ C8 H) as HB; clear H end;
    norm_bc; rewrite ?mod_small64 in * by lia.
    all: try (match goal with H: ?a <> ?b |- _ => destruct (step8 _ _ KE KE8 H) end).
    all: try (match goal with H: ?a = ?b |- _ => constr_eq a k; constr_eq b e; subst e end).
    all: first [ exists k; solve [fin_all]
               | exists (k+8), e; solve [fin_all] ].
  - (* 0x15e288: tail byte loop *)
    destruct PRE as (k & N64 & KLE & X0 & X2 & X1 & NM & MEM & SP & X30).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ post_or k
               | exists (k+1); solve [fin_all] ].
Qed.
