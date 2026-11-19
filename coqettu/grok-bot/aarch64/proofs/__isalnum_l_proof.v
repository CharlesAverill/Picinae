(* __isalnum_l -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64: a single tail branch to isalnum

   SEMANTICS
   ---------
   __isalnum_l is compiled to one instruction, b isalnum: the locale argument (if
   any) is ignored and the arguments are passed through unchanged, as in
   musl (the _l variants ignore their locale_t; iswblank is isblank;
   strcoll and wcscoll are strcmp and wcscmp in musl C locale handling).

   SPECIFICATION
   -------------
   Exactly the specification of isalnum (see proofs/isalnum_proof.v): the
   theorem below has the same hypotheses and the same invariant set as
   isalnum_partial_correctness, started at the entry of __isalnum_l; it is proved
   from that theorem with GrokTail.tailcall_satisfies_all.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            __isalnum_l at 0x1ee14 (ELF vaddr); 0x11ee14 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/__isalnum_l_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input/Output: as for isalnum; the program must contain both __isalnum_l and
            isalnum (and whatever isalnum itself calls).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import __isalnum_l_armv8 isalnum_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import isalnum_proof.
Import ARM8Notations.
Open Scope N.

Theorem __isalnum_l_nwc: ∀ s2 s1, __isalnum_l_armv8 s1 = __isalnum_l_armv8 s2.
Proof. reflexivity. Qed.

Theorem __isalnum_l_welltyped: welltyped_prog arm8typctx __isalnum_l_armv8.
Proof. Picinae_typecheck. Qed.

Theorem __isalnum_l_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PW: __isalnum_l_armv8 ⊆2 prog) (PROG: isalnum_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee14, s))
    (MDL: models arm8typctx s) (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (isalnum_invs sp mem raddr c d) (isalnum_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog _ _) with (a0 := 0x11ee14) (a1 := 0x11edec)
    (P := fun s => (models arm8typctx s) /\ (s R_SP = sp) /\ (s V_MEM64 = mem) /\ (s R_X30 = raddr) /\ (s R_X0 = c) /\ (s R_X1 = d)) (s := s).
  - intros [[aa|ii] s1] t1 t2; reflexivity.
  - intros [[aa|ii] s1] t1 t2; reflexivity.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro s1. apply PW. reflexivity.
  - intros s1 s2 E HP. repeat match goal with H: _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end; try (rewrite <- !E; assumption); try assumption.
    all: try (intros vv ww CV; rewrite <- E; eauto).
  - intros s1 t1 xs1 START HP. repeat match goal with H: _ /\ _ |- _ => destruct H end.
    eapply isalnum_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
