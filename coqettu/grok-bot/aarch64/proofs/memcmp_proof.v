(* memcmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/memcmp.c is

       int memcmp(const void *vl, const void *vr, size_t n)
       { const unsigned char *l=vl, *r=vr;
         for (; n && *l == *r; n--, l++, r++);
         return n ? *l-*r : 0; }

   compiled to a 12-instruction loop.  The loop head 0x15e2a8 is also the
   entry point: CBZ X2 returns 0; otherwise it loads one byte from each of
   X0/X1, decrements X2, increments both pointers, and loops back with
   B.EQ while the bytes are equal.  At the first difference it returns
   W0 = W3 - W4 (the two unsigned bytes subtracted in 32 bits).

   SPECIFICATION (man 3 memcmp, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            int memcmp(const void s1[.n], const void s2[.n], size_t n);

     DESCRIPTION
            The  memcmp()  function compares the first n bytes (each interpreted as
            unsigned char) of the memory areas s1 and s2.

     RETURN VALUE
            The memcmp() function returns an integer less than, equal to, or greater
            than zero if the first n bytes of s1 is found, respectively, to be  less
            than, to match, or be greater than the first n bytes of s2.

            For  a  nonzero return value, the sign is determined by the sign of the
            difference between the first pair  of  bytes  (interpreted  as  unsigned
            char) that differ in s1 and s2.

            If n is zero, the return value is zero.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memcmp at 0x5e2a8 (ELF vaddr); 0x15e2a8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py
            from picinae-llm/tools/ghidra-lifter (repo HEAD a4bae9c), options
            --globalAddressing --typeCheck; see ../lifted/memcmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1, X1 = s2, X2 = n; X30 = return address; m = memory on entry.
   Output:  If execution reaches the RET (0x15e2d4), there is a k <= n such
            that bytes s1+i and s2+i agree for all i < k, and either
              k = n and X0 = 0, or
              k < n, the bytes b1 = m[s1+k] and b2 = m[s2+k] differ, and
              X0 = (b1 - b2) mod 2^32 (zero-extended W0),
            so the int return value toZ32(X0) equals b1 - b2 and its sign is
            the unsigned byte comparison (memcmp_result_sign).  Memory, SP, X30
            and all AAPCS64 callee-saved registers are unchanged.
            Addresses wrap modulo 2^64 (s1+i means (s1+i) mod 2^64).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memcmp_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem memcmp_nwc: ∀ s2 s1, memcmp_armv8 s1 = memcmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem memcmp_welltyped: welltyped_prog arm8typctx memcmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem memcmp_preserves_memory:
  forall_endstates memcmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem memcmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memcmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memcmp_preserves_x30:
  forall_endstates memcmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)

Section Invariants.
  Variables (sp mem raddr p q n : N).

  Definition memcmp_post (s:store) :=
    ∃ k, k <= n /\ mem_eq mem p q k /\
      ((k = n /\ s R_X0 = 0) \/
       (k < n /\ mem Ⓑ[p+k] ≠ mem Ⓑ[q+k] /\
        s R_X0 = msub 32 (mem Ⓑ[p+k]) (mem Ⓑ[q+k]))) /\
      s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry and loop head: cbz x2 *)
    | 0x15e2a8 => Inv 0 (∃ k, k <= n /\ s R_X0 = p ⊕ k /\ s R_X1 = q ⊕ k /\ s R_X2 = n - k /\
                         mem_eq mem p q k /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15e2d4 => Post 0 (memcmp_post s)
    | _ => NoInv
    end.

  Definition memcmp_exits := make_exits 0 memcmp_armv8 invs.
  Definition memcmp_invs := make_invs 0 memcmp_armv8 invs.
End Invariants.

(* ---------------------------------------------------------------------- *)
(* Partial correctness                                                     *)

Theorem memcmp_partial_correctness:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: memcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e2a8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (memcmp_invs sp mem raddr p q n) (memcmp_exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memcmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memcmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step.
  pose proof (MDL R_X0 64 eq_refl). pose proof (MDL R_X1 64 eq_refl).
  exists 0. rewrite !N.add_0_r, !N.mod_small, N.sub_0_r by (subst; assumption).
  repeat split; try assumption. apply N.le_0_l. apply mem_eq_0.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (k & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
  pose proof (MDL1 R_X2 64 eq_refl) as X2B. rewrite X2 in X2B.
  arm8_step.
  (* n - k = 0: return 0 *)
  - repeat arm8_step.
    apply N.eqb_eq in BC. exists k. repeat split; try assumption.
    left. split. lia. reflexivity.
  - apply N.eqb_neq in BC.
    repeat arm8_step.
    (* bytes equal: loop *)
    + apply N.eqb_eq in BC0. exists (k+1). repeat split; try assumption.
      lia. f_equal; lia. f_equal; lia.
      rewrite msub_small by lia. lia.
      apply mem_eq_succ; assumption.
    (* bytes differ: return the difference *)
    + apply N.eqb_neq in BC0.
      exists k. repeat split; try assumption.
      right. repeat split; try assumption. lia.
Qed.

(* The int result (low 32 bits of X0, signed) has the sign of the
   unsigned-byte comparison, as the man page requires. *)
Theorem memcmp_result_sign:
  ∀ (m:memory) (p q k:N), Z.compare (toZ 32 (msub 32 (m Ⓑ[p+k]) (m Ⓑ[q+k]))) 0%Z = N.compare (m Ⓑ[p+k]) (m Ⓑ[q+k]).
Proof. intros. apply msub32_bytes_sign; apply byte_lt8. Qed.

(* A non-zero difference is reported as non-zero. *)
Theorem memcmp_result_nonzero:
  ∀ m p q k, m Ⓑ[p+k] ≠ m Ⓑ[q+k] -> msub 32 (m Ⓑ[p+k]) (m Ⓑ[q+k]) ≠ 0.
Proof.
  intros m p q k NE H. apply NE.
  pose proof (memcmp_result_sign m p q k) as S. rewrite H in S.
  apply N.compare_eq_iff. rewrite <- S. reflexivity.
Qed.
