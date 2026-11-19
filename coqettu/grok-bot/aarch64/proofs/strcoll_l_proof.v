(* strcoll_l -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64: a single tail branch to strcmp (same machine code as __strcoll_l)

   SEMANTICS
   ---------
   strcoll_l is compiled to one instruction, b strcmp: the locale argument (if
   any) is ignored and the arguments are passed through unchanged, as in
   musl (the _l variants ignore their locale_t; iswblank is isblank;
   strcoll and wcscoll are strcmp and wcscmp in musl C locale handling).

   SPECIFICATION
   -------------
   Exactly the specification of strcmp (see proofs/strcmp_proof.v): the
   theorem below has the same hypotheses and the same invariant set as
   strcmp_partial_correctness, started at the entry of strcoll_l; it is proved
   from that theorem with GrokTail.tailcall_satisfies_all.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strcoll_l at 0x28060 (ELF vaddr); 0x128060 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/strcoll_l_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input/Output: as for strcmp; the program must contain both strcoll_l and
            strcmp (and whatever strcmp itself calls).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import strcoll_l_armv8 strcmp_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import strcmp_proof.
Import ARM8Notations.
Open Scope N.

Theorem strcoll_l_nwc: ∀ s2 s1, strcoll_l_armv8 s1 = strcoll_l_armv8 s2.
Proof. reflexivity. Qed.

Theorem strcoll_l_welltyped: welltyped_prog arm8typctx strcoll_l_armv8.
Proof. Picinae_typecheck. Qed.

Theorem strcoll_l_partial_correctness:
  ∀ prog s sp mem raddr p q t xs'
    (PW: strcoll_l_armv8 ⊆2 prog) (PROG: strcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x128060, s))
    (MDL: models arm8typctx s) (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p) (X1: s R_X1 = q),
  satisfies_all prog (strcmp_invs sp mem raddr p q) (strcmp_exits sp mem raddr p q) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog _ _) with (a0 := 0x128060) (a1 := 0x15eca4)
    (P := fun s => (models arm8typctx s) /\ (s R_SP = sp) /\ (s V_MEM64 = mem) /\ (s R_X30 = raddr) /\ (s R_X0 = p) /\ (s R_X1 = q)) (s := s).
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
    eapply strcmp_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
