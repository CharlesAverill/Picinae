(* bcmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (tail call to memcmp)

   SEMANTICS
   ---------
   musl's src/string/bcmp.c:
       int bcmp(const void *s1, const void *s2, size_t n) {
           return memcmp(s1, s2, n);
       }
   compiled as a single instruction "b memcmp" (0x15e2a8); the program here
   is both lifts (bcmp_prog) and the memcmp loop is re-proved inside it.

   SPECIFICATION (man 3 bcmp, Linux man-pages 6.9.1)
   -------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            int bcmp(const void s1[.n], const void s2[.n], size_t n);
     DESCRIPTION
            The bcmp() function compares the two byte sequences s1 and s2 of
            length n each.  If they are equal, and in particular if n is
            zero, bcmp() returns 0.  Otherwise, it returns a nonzero result.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            bcmp at 0x5e0e8 (ELF vaddr); 0x15e0e8 in Ghidra (image base 0x100000);
            memcmp at 0x5e2a8 / 0x15e2a8
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/bcmp_armv8.v and
            ../lifted/memcmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 (p), X1 = s2 (q), X2 = n; X30 = return address.
   Output:  If execution reaches memcmp's RET (0x15e2d4), memcmp_post holds
            (memcmp_proof.v): there is k <= n with the first k bytes equal and
            either k = n and X0 = 0, or k < n, the bytes at p+k and q+k differ
            and X0 = their difference mod 2^32, which is nonzero
            (memcmp_proof.memcmp_result_nonzero).  Memory, SP, X30 and all
            AAPCS64 callee-saved registers are unchanged
            (bcmp_preserves_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require bcmp_armv8 memcmp_armv8.
From Grok.lib Require Import GrokCommon.
From Grok.proofs Require memcmp_proof.
Import ARM8Notations.
Open Scope N.

(* bcmp is a single tail branch to memcmp; the program is both lifts. *)
Definition bcmp_prog : program := updateall2 bcmp_armv8.bcmp_armv8 memcmp_armv8.memcmp_armv8.

Lemma bcmp_prog_mono: ∀ prog, bcmp_armv8.bcmp_armv8 ⊆2 prog -> memcmp_armv8.memcmp_armv8 ⊆2 prog ->
  bcmp_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold bcmp_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

Theorem bcmp_prog_welltyped: welltyped_prog arm8typctx bcmp_prog.
Proof.
  intros s a. unfold bcmp_prog, updateall2, updateall.
  destruct (memcmp_armv8.memcmp_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (memcmp_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply bcmp_armv8.welltyped.
Qed.

Theorem bcmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates bcmp_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* bcmp entry: b memcmp *)
    | 0x15e0e8 => Inv 0 (s R_X0 = p /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* memcmp entry and loop head *)
    | 0x15e2a8 => Inv 0 (∃ k, k <= n /\ s R_X0 = p ⊕ k /\ s R_X1 = q ⊕ k /\ s R_X2 = n - k /\
                         mem_eq mem p q k /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* memcmp ret *)
    | 0x15e2d4 => Post 0 (memcmp_proof.memcmp_post sp mem raddr p q n s)
    | _ => NoInv
    end.
  Definition bcmp_exits := make_exits 0 bcmp_prog invs.
  Definition bcmp_invs := make_invs 0 bcmp_prog invs.
End Invariants.

Theorem bcmp_partial_correctness:
  ∀ prog s sp mem raddr p q n t xs'
    (P1: bcmp_armv8.bcmp_armv8 ⊆2 prog) (P0: memcmp_armv8.memcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e0e8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (bcmp_invs sp mem raddr p q n) (bcmp_exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=bcmp_prog). apply bcmp_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold bcmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply bcmp_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* bcmp: branch to memcmp with k = 0 *)
    destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X1 64 eq_refl) as Q64.
    rewrite X0 in P64. rewrite X1 in Q64.
    arm8_step.
    exists 0. rewrite !N.add_0_r, !N.mod_small, N.sub_0_r by assumption.
    repeat split; try assumption. apply N.le_0_l. apply mem_eq_0.
  - destruct PRE as (k & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
    pose proof (MDL1 R_X2 64 eq_refl) as X2B. rewrite X2 in X2B.
    arm8_step.
    + repeat arm8_step.
      apply N.eqb_eq in BC. exists k. repeat split; try assumption.
      left. split. lia. reflexivity.
    + apply N.eqb_neq in BC.
      repeat arm8_step.
      * apply N.eqb_eq in BC0. exists (k+1). repeat split; try assumption.
        lia. f_equal; lia. f_equal; lia.
        rewrite msub_small by lia. lia.
        apply mem_eq_succ; assumption.
      * apply N.eqb_neq in BC0.
        exists k. repeat split; try assumption.
        right. repeat split; try assumption. lia.
Qed.
