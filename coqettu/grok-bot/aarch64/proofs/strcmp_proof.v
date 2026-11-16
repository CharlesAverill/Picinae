(* strcmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/strcmp.c is

       int strcmp(const char *l, const char *r)
       { for (; *l==*r && *l; l++, r++);
         return (unsigned char)l[0] - (unsigned char)r[0]; }   [casts paraphrased]

   compiled with an index register: X2 = 0; loop: W4 = l[X2], W3 = r[X2],
   X2++, CMP W4,W3; B.NE to the exit; CBNZ W3 back to the loop; on equal
   zero bytes W4 is cleared; the exit computes W0 = W4 - W3.

   SPECIFICATION (man 3 strcmp, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            int strcmp(const char *s1, const char *s2);

     DESCRIPTION
            The strcmp() function compares the two strings s1 and s2.  The locale is
            not  taken into account (for a locale-aware comparison, see strcoll(3)).
            The comparison is done using unsigned characters.

            strcmp() returns an integer indicating the result of the comparison,  as
            follows:
            •  0, if the s1 and s2 are equal;
            •  a negative value if s1 is less than s2;
            •  a positive value if s1 is greater than s2.

     RETURN VALUE
            The  strcmp() and strncmp() functions return an integer less than, equal
            to, or greater than zero if s1 (or the first n bytes thereof) is  found,
            respectively, to be less than, to match, or be greater than s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strcmp at 0x5eca4 (ELF vaddr); 0x15eca4 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py
            from picinae-llm/tools/ghidra-lifter (repo HEAD a4bae9c), options
            --globalAddressing --typeCheck; see ../lifted/strcmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1, X1 = s2; X30 = return address; m = memory on entry.
            Nothing is assumed about the strings.
   Output:  If execution reaches the RET (0x15ecc8), there is a k such that
            the first k bytes of s1 and s2 agree and are non-zero, and at
            index k either the bytes b1 = m[s1+k], b2 = m[s2+k] differ, or both
            are 0 (the strings are equal); X0 = (b1 - b2) mod 2^32, so the int
            result toZ32(X0) = b1 - b2, whose sign is the unsigned byte
            comparison (strcmp_result_sign); it is 0 exactly when the strings
            are equal.  Memory, SP, X30 and the AAPCS64 callee-saved registers
            are unchanged.  Addresses wrap modulo 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import strcmp_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem strcmp_nwc: ∀ s2 s1, strcmp_armv8 s1 = strcmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem strcmp_welltyped: welltyped_prog arm8typctx strcmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem strcmp_preserves_memory:
  forall_endstates strcmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strcmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates strcmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem strcmp_preserves_x30:
  forall_endstates strcmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)

Section Invariants.
  Variables (sp mem raddr p q : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry *)
    | 0x15eca4 => Inv 0 (s R_X0 = p /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* loop head: ldrb w4,[x0,x2] *)
    | 0x15eca8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = q /\ s R_X2 = k /\
                         mem_eq mem p q k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15ecc8 => Post 0 (∃ k, mem_eq mem p q k /\ nilfree mem p k /\
                    (mem Ⓑ[p+k] ≠ mem Ⓑ[q+k] \/ mem Ⓑ[p+k] = 0 /\ mem Ⓑ[q+k] = 0) /\
                    s R_X0 = msub 32 (mem Ⓑ[p+k]) (mem Ⓑ[q+k]) /\
                    s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition strcmp_exits := make_exits 0 strcmp_armv8 invs.
  Definition strcmp_invs := make_invs 0 strcmp_armv8 invs.
End Invariants.


Theorem strcmp_partial_correctness:
  ∀ prog s sp mem raddr p q t xs'
    (PROG: strcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eca4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q),
  satisfies_all prog (strcmp_invs sp mem raddr p q) (strcmp_exits sp mem raddr p q) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strcmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold strcmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    repeat arm8_step.
    exists 0. repeat split; try assumption. all: first [apply mem_eq_0 | apply nilfree_0 | reflexivity].
  - destruct PRE as (k & KLT & X0 & X1 & X2 & EQ & NF & MEM & SP & X30).
    repeat arm8_step.
    + (* equal non-zero bytes: loop *)
      apply N.eqb_eq in BC. apply cbnz32_true in BC0; [|apply byte_lt32].
      destruct (N.lt_ge_cases (k+1) (2^64)) as [LT|GE].
      * exists (k+1). repeat split; try assumption.
        rewrite N.add_comm. apply N.mod_small. exact LT.
        apply mem_eq_succ; assumption.
        apply nilfree_succ. assumption. rewrite BC. exact BC0.
      * exists 0. repeat split; try assumption.
        all: first [ apply mem_eq_0 | apply nilfree_0 | reflexivity
                   | replace (1+k) with (2^64) by lia; reflexivity ].
    + (* equal zero bytes: return 0 *)
      apply N.eqb_eq in BC. apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; try assumption.
      right. rewrite BC. split; assumption.
      rewrite BC, BC0. reflexivity.
    + (* differing bytes *)
      apply N.eqb_neq in BC.
      exists k. repeat split; try assumption. left. assumption.
Qed.

(* The int result has the sign of the unsigned comparison of the first
   differing bytes (and is 0 when both are the terminator). *)
Theorem strcmp_result_sign:
  ∀ (m:memory) (p q k:N),
  Z.compare (toZ 32 (msub 32 (m Ⓑ[p+k]) (m Ⓑ[q+k]))) 0%Z = N.compare (m Ⓑ[p+k]) (m Ⓑ[q+k]).
Proof. intros. apply msub32_bytes_sign; apply byte_lt8. Qed.
