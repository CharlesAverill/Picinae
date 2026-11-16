(* pthread_equal -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/thread/pthread_equal.c:
       int pthread_equal(pthread_t a, pthread_t b) { return a==b; }
   compiled to  cmp x0,x1; cset w0,eq; ret  (pthread_t is a 64-bit pointer).

   SPECIFICATION (man 3 pthread_equal, Linux man-pages 6.9.1)
   ----------------------------------------------------------
     SYNOPSIS
            #include <pthread.h>
            int pthread_equal(pthread_t t1, pthread_t t2);
     DESCRIPTION
            The pthread_equal() function compares two thread identifiers.
     RETURN VALUE
            If the two thread IDs are equal, pthread_equal() returns a nonzero
            value; otherwise, it returns 0.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            pthread_equal at 0x62f00 (ELF vaddr); 0x162f00 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/pthread_equal_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = t1, X1 = t2 (64-bit values); X30 = return address.
   Output:  If execution reaches the RET (0x162f08): X0 = 1 if t1 = t2 and
            X0 = 0 otherwise.  Memory, SP, X30 and the AAPCS64 callee-saved
            registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import pthread_equal_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Theorem pthread_equal_welltyped: welltyped_prog arm8typctx pthread_equal_armv8.
Proof. Picinae_typecheck. Qed.

Theorem pthread_equal_preserves_memory:
  forall_endstates pthread_equal_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem pthread_equal_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates pthread_equal_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem pthread_equal_preserves_x30:
  forall_endstates pthread_equal_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x162f00 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x162f08 => Post 0 (s R_X0 = (if c =? d then 1 else 0) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition peq_exits := make_exits 0 pthread_equal_armv8 invs.
  Definition peq_invs := make_invs 0 pthread_equal_armv8 invs.
End Invariants.

Theorem pthread_equal_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: pthread_equal_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x162f00, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (peq_invs sp mem raddr c d) (peq_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=pthread_equal_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold peq_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply pthread_equal_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
Qed.
