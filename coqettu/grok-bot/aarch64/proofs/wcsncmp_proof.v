(* wcsncmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/wcsncmp.c:
       for (; n && l[0]==r[0] && l[0] && r[0]; n--, l++, r++);
       return n ? (l[0] < r[0] ? -1 : l[0] > r[0]) : 0;
   (written with l[0] for the dereference of l).  wchar_t is unsigned int on
   aarch64, so the final comparison is unsigned (cset w0,hi; csinv w0,w0,wzr,cs).
   The loop test uses ccmp, which the lifter models with an internal
   conditional jump; GrokStep.grok_step steps through it.  The proof needs
   the BOOL_NEGATE lifter fix (../lifter/README_GROK.md).

   SPECIFICATION (man 3 wcsncmp, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            int wcsncmp(const wchar_t s1[.n], const wchar_t s2[.n], size_t n);

     DESCRIPTION
            The wcsncmp() function is the wide-character equivalent of the
            strncmp(3) function.  It compares the wide-character string pointed
            to by s1 and the wide-character string pointed to by s2, but at
            most n wide characters from each string.  In each string, the
            comparison extends only up to the first occurrence of a null wide
            character (L'\0'), if any.

     RETURN VALUE
            The wcsncmp() function returns zero if the wide-character strings
            at s1 and s2, truncated to at most length n, are equal.  It returns
            an integer greater than zero if at the first differing position i
            (i < n), the corresponding wide-character s1[i] is greater than
            s2[i].  It returns an integer less than zero if at the first
            differing position i (i < n), the corresponding wide-character
            s1[i] is less than s2[i].

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcsncmp at 0x5fd34 (ELF vaddr); 0x15fd34 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcsncmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 = p, X1 = s2 = q, X2 = n; X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x15fd64), then either
              - X0 = 0 and for all i < n the 32-bit words m[p+4i] = m[q+4i]
                and are non-zero (no terminator within the first n), or
              - there is k < n such that for all i < k the words agree and are
                non-zero, at k they differ or m[p+4k] = 0 (end of s1), and
                X0 = wcmp_result m[p+4k] m[q+4k]: 2^32-1 (int -1) if
                m[p+4k] < m[q+4k] (unsigned), 1 if greater, 0 if equal (both
                strings end at k).
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.  Addresses wrap modulo 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wcsncmp_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem wcsncmp_nwc: ∀ s2 s1, wcsncmp_armv8 s1 = wcsncmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem wcsncmp_welltyped: welltyped_prog arm8typctx wcsncmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wcsncmp_preserves_memory:
  forall_endstates wcsncmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcsncmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wcsncmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wcsncmp_preserves_x30:
  forall_endstates wcsncmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

(* The first k wide characters at p and q are equal and non-zero. *)
Definition wmem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] = m Ⓓ[q + 4*i] /\ m Ⓓ[p + 4*i] ≠ 0.

Lemma wmem_eq_0: ∀ m p q, wmem_eq m p q 0.
Proof. unfold wmem_eq. intros. lia. Qed.

Lemma wmem_eq_succ: ∀ m p q k, wmem_eq m p q k -> m Ⓓ[p + 4*k] = m Ⓓ[q + 4*k] -> m Ⓓ[p + 4*k] ≠ 0 -> wmem_eq m p q (k+1).
Proof.
  unfold wmem_eq. intros m p q k E B Z i I.
  destruct (N.lt_ge_cases i k). apply E; assumption. replace i with k by lia. split; assumption.
Qed.

(* wchar_t is unsigned int on aarch64: -1 (as a 32-bit int) if a < b, else 1. *)
Definition wcmp_result (a b:N) : N := if a <? b then 2^32 - 1 else if b <? a then 1 else 0.


Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15fd34 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X1 = q ⊕ 4*k /\
                         s R_X2 = n - k /\ wmem_eq mem p q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fd64 => Post 0 ((s R_X0 = 0 /\ wmem_eq mem p q n \/
                          (∃ k, k < n /\ wmem_eq mem p q k /\ (mem Ⓓ[p + 4*k] ≠ mem Ⓓ[q + 4*k] \/ mem Ⓓ[p + 4*k] = 0) /\
                                s R_X0 = wcmp_result (mem Ⓓ[p + 4*k]) (mem Ⓓ[q + 4*k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wcsncmp_exits := make_exits 0 wcsncmp_armv8 invs.
  Definition wcsncmp_invs := make_invs 0 wcsncmp_armv8 invs.
End Invariants.


Theorem wcsncmp_partial_correctness:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: wcsncmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fd34, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (wcsncmp_invs sp mem raddr p q n) (wcsncmp_exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcsncmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wcsncmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step.
    pose proof (MDL R_X0 64 eq_refl) as P64. pose proof (MDL R_X1 64 eq_refl) as Q64.
    pose proof (MDL R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X1 in Q64. rewrite X2 in N64. simpl in P64, Q64, N64.
    exists 0. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r, !N.mod_small by assumption.
    repeat split; try assumption; try lia. all: try apply wmem_eq_0.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (k & N64 & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
  repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    | H: (_ <=? _) = true |- _ => apply N.leb_le in H
    | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
    end.
  1: { split; [|repeat split; assumption]. left. split. reflexivity. replace n with k by lia. exact EQ. }
  all: first
    [ exists (k+1); splits; try reflexivity; try assumption; try lia;
      first [ (f_equal; lia) | (rewrite msub_small by lia; lia)
            | (apply wmem_eq_succ; [assumption | lia | assumption]) ]
    | split; [|repeat split; assumption]; right; exists k; splits; try assumption; try lia;
      first [ (right; assumption) | (left; lia) |
        (unfold wcmp_result;
         repeat match goal with |- context [?a <? ?b] => destruct (a <? b) eqn:?
                              | |- context [?a =? ?b] => destruct (a =? b) eqn:? end;
         rewrite ?N.ltb_lt, ?N.ltb_ge, ?N.eqb_eq, ?N.eqb_neq in *; lia) ] ].
Qed.
