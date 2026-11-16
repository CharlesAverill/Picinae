(* wmemcmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/wmemcmp.c:
       for (; n && l[0]==r[0]; n--, l++, r++);
       return n ? (l[0] < r[0] ? -1 : l[0] > r[0]) : 0;    [written with l[0] for *l]
   On aarch64 wchar_t is unsigned int, so the comparison is unsigned on 32-bit
   words: the binary uses cset w0,hi; csinv w0,w0,wzr,cs.  The proof needs the
   BOOL_NEGATE lifter fix (see ../lifter/README_GROK.md): upstream lifts the
   inverted flag in cset as a bitwise NOT.

   SPECIFICATION (man 3 wmemcmp, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            int wmemcmp(const wchar_t s1[.n], const wchar_t s2[.n], size_t n);

     DESCRIPTION
            The wmemcmp() function is the wide-character equivalent of the
            memcmp(3) function.  It compares the n wide-characters starting at
            s1 and the n wide-characters starting at s2.

     RETURN VALUE
            The wmemcmp() function returns zero if the wide-character arrays of
            size n at s1 and s2 are equal.  It returns an integer greater than
            zero if at the first differing position i (i < n), the
            corresponding wide-character s1[i] is greater than s2[i].  It
            returns an integer less than zero if at the first differing
            position i (i < n), the corresponding wide-character s1[i] is less
            than s2[i].

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wmemcmp at 0x601f8 (ELF vaddr); 0x1601f8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wmemcmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 = p, X1 = s2 = q, X2 = n; X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x160228), then either
              - X0 = 0 and the 32-bit words m[p+4i], m[q+4i] agree for all i < n, or
              - there is k < n such that the words agree for all i < k, they
                differ at k, and X0 = wcmp_result m[p+4k] m[q+4k], i.e.
                X0 = 2^32-1 (int -1, zero-extended) if m[p+4k] < m[q+4k]
                (unsigned), and X0 = 1 otherwise.
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.  Addresses wrap modulo 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemcmp_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem wmemcmp_nwc: ∀ s2 s1, wmemcmp_armv8 s1 = wmemcmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem wmemcmp_welltyped: welltyped_prog arm8typctx wmemcmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemcmp_preserves_memory:
  forall_endstates wmemcmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wmemcmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wmemcmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wmemcmp_preserves_x30:
  forall_endstates wmemcmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

(* The first k wide characters at p and q are equal. *)
Definition wmem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] = m Ⓓ[q + 4*i].

Lemma wmem_eq_0: ∀ m p q, wmem_eq m p q 0.
Proof. unfold wmem_eq. intros. lia. Qed.

Lemma wmem_eq_succ: ∀ m p q k, wmem_eq m p q k -> m Ⓓ[p + 4*k] = m Ⓓ[q + 4*k] -> wmem_eq m p q (k+1).
Proof.
  unfold wmem_eq. intros m p q k E B i I.
  destruct (N.lt_ge_cases i k). apply E; assumption. replace i with k by lia. exact B.
Qed.

(* wchar_t is unsigned int on aarch64: -1 (as a 32-bit int) if a < b, else 1. *)
Definition wcmp_result (a b:N) : N := if a <? b then 2^32 - 1 else 1.

Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x1601f8 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X1 = q ⊕ 4*k /\
                         s R_X2 = n - k /\ wmem_eq mem p q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160228 => Post 0 ((s R_X0 = 0 /\ wmem_eq mem p q n \/
                          (∃ k, k < n /\ wmem_eq mem p q k /\ mem Ⓓ[p + 4*k] ≠ mem Ⓓ[q + 4*k] /\
                                s R_X0 = wcmp_result (mem Ⓓ[p + 4*k]) (mem Ⓓ[q + 4*k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wmemcmp_exits := make_exits 0 wmemcmp_armv8 invs.
  Definition wmemcmp_invs := make_invs 0 wmemcmp_armv8 invs.
End Invariants.


Theorem wmemcmp_partial_correctness:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: wmemcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1601f8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (wmemcmp_invs sp mem raddr p q n) (wmemcmp_exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemcmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wmemcmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step.
    pose proof (MDL R_X0 64 eq_refl) as P64. pose proof (MDL R_X1 64 eq_refl) as Q64.
    pose proof (MDL R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X1 in Q64. rewrite X2 in N64. simpl in P64, Q64, N64.
    exists 0. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r, !N.mod_small by assumption.
    repeat split; try assumption; try lia. apply wmem_eq_0.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemcmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (k & N64 & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
  repeat arm8_step.
  - apply N.eqb_eq in BC. split; [|repeat split; assumption].
    left. split. reflexivity. replace n with k by lia. exact EQ.
  - apply N.eqb_eq in BC0. apply N.eqb_neq in BC. exists (k+1).
    repeat split; try assumption; try lia.
    all: first [ (f_equal; lia) | (rewrite msub_small by lia; lia) | (apply wmem_eq_succ; assumption) ].
  - apply N.eqb_neq in BC0, BC. apply N.leb_le in BC1. split; [|repeat split; assumption].
    right. exists k. repeat split; try assumption; try lia.
    unfold wcmp_result. rewrite (proj2 (N.ltb_ge _ _)) by lia. reflexivity.
  - apply N.eqb_neq in BC0, BC. apply N.leb_gt in BC1. split; [|repeat split; assumption].
    right. exists k. repeat split; try assumption; try lia.
    unfold wcmp_result. rewrite (proj2 (N.ltb_lt _ _)) by lia. reflexivity.
Qed.
