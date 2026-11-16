(* strncmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/strncmp.c (l, r are the arguments as unsigned char
   pointers):
       if (!n--) return 0;
       for (; l[0] && r[0] && n && l[0] == r[0] ; l++, r++, n--);
       return l[0] - r[0];
   The binary keeps an index X3 = k and X2 = n-1; the loop test is a chain of
   cmp/ccmp/cbz/ccmp (stepped with GrokStep.grok_step).  The result is the
   32-bit difference W4 - W5 of the two bytes at the stopping index.

   SPECIFICATION (man 3 strncmp, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <string.h>
            int strncmp(const char s1[.n], const char s2[.n], size_t n);

     DESCRIPTION
            The strcmp() function compares the two strings s1 and s2.  The
            locale is not taken into account.  The comparison is done using
            unsigned characters.
            The strncmp() function is similar, except it compares only the
            first (at most) n bytes of s1 and s2.

     RETURN VALUE
            The strcmp() and strncmp() functions return an integer less than,
            equal to, or greater than zero if s1 (or the first n bytes thereof)
            is found, respectively, to be less than, to match, or be greater
            than s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strncmp at 0x5f110 (ELF vaddr); 0x15f110 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strncmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 = p, X1 = s2 = q, X2 = n; X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x15f140), then either
              - n = 0 and X0 = 0, or
              - there is k < n such that bytes p+i and q+i agree and are
                non-zero for all i < k, and at k the bytes differ, or the byte
                of s1 is 0 (end of both strings or of s1), or k = n-1 (last
                byte allowed), and X0 = msub 32 m[p+k] m[q+k], i.e. as a
                signed int X0 = m[p+k] - m[q+k] (strncmp_result_value).
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.  Note: s1 and s2 are indexed without wraparound
            (p+k with k < n < 2^64, reduced mod 2^64 by memory access).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import strncmp_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem strncmp_nwc: ∀ s2 s1, strncmp_armv8 s1 = strncmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem strncmp_welltyped: welltyped_prog arm8typctx strncmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem strncmp_preserves_memory:
  forall_endstates strncmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strncmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates strncmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem strncmp_preserves_x30:
  forall_endstates strncmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f110 => Inv 0 (s R_X0 = p /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f11c => Inv 0 (∃ k, n < 2^64 /\ 0 < n /\ k < n /\ s R_X0 = p /\ s R_X1 = q /\
                         s R_X2 = n - 1 /\ s R_X3 = k /\
                         mem_eq mem p q k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f140 => Post 0 ((s R_X0 = 0 /\ n = 0 \/
                          (∃ k, k < n /\ mem_eq mem p q k /\ nilfree mem p k /\
                                (mem Ⓑ[p + k] ≠ mem Ⓑ[q + k] \/ mem Ⓑ[p + k] = 0 \/ k = n - 1) /\
                                s R_X0 = msub 32 (mem Ⓑ[p + k]) (mem Ⓑ[q + k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition strncmp_exits := make_exits 0 strncmp_armv8 invs.
  Definition strncmp_invs := make_invs 0 strncmp_armv8 invs.
End Invariants.


Theorem strncmp_partial_correctness:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: strncmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f110, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (strncmp_invs sp mem raddr p q n) (strncmp_exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strncmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold strncmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    end.
    + split; [|splits; assumption]. left. split; [reflexivity|assumption].
    + exists 0. splits; try assumption; try reflexivity; try lia.
      all: first [ (rewrite msub_small by lia; reflexivity) | apply mem_eq_0 | apply nilfree_0 ].
  - destruct PRE as (k & N64 & NPOS & KLT & X0 & X1 & X2 & X3 & EQ & NF & MEM & SP & X30).
    repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    end.
    all: first
      [ exists (k+1); splits; try reflexivity; try assumption; try lia;
        first [ (rewrite N.mod_small by lia; lia) | (apply mem_eq_succ; assumption)
              | (apply nilfree_succ; assumption) ]
      | split; [|splits; reflexivity || assumption]; right; exists k;
        splits; try assumption; try reflexivity; try lia ].
Qed.

(* The returned int is the difference of the two unsigned chars at k. *)
Theorem strncmp_result_value:
  ∀ m a b, toZ 32 (msub 32 (m Ⓑ[a]) (m Ⓑ[b])) = (Z.of_N (m Ⓑ[a]) - Z.of_N (m Ⓑ[b]))%Z.
Proof. intros. apply msub32_bytes_toZ; apply byte_lt8. Qed.
