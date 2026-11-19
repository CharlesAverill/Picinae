(* islower_l -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64: a single tail branch to islower (same machine code as __islower_l)

   SEMANTICS
   ---------
   islower_l is compiled to one instruction, b islower: the locale argument (if
   any) is ignored and the arguments are passed through unchanged, as in
   musl (the _l variants ignore their locale_t; iswblank is isblank;
   strcoll and wcscoll are strcmp and wcscmp in musl C locale handling).

   SPECIFICATION
   -------------
   Exactly the specification of islower (see proofs/islower_proof.v): the
   theorem below has the same hypotheses and the same invariant set as
   islower_partial_correctness, started at the entry of islower_l; it is proved
   from that theorem with GrokTail.tailcall_satisfies_all.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            islower_l at 0x1ee9c (ELF vaddr); 0x11ee9c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/islower_l_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input/Output: as for islower; the program must contain both islower_l and
            islower (and whatever islower itself calls).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import islower_l_armv8 islower_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import islower_proof.
Import ARM8Notations.
Open Scope N.

Theorem islower_l_nwc: ∀ s2 s1, islower_l_armv8 s1 = islower_l_armv8 s2.
Proof. reflexivity. Qed.

Theorem islower_l_welltyped: welltyped_prog arm8typctx islower_l_armv8.
Proof. Picinae_typecheck. Qed.

Theorem islower_l_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PW: islower_l_armv8 ⊆2 prog) (PROG: islower_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee9c, s))
    (MDL: models arm8typctx s) (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (islower_invs sp mem raddr c) (islower_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog _ _) with (a0 := 0x11ee9c) (a1 := 0x11ee8c)
    (P := fun s => (models arm8typctx s) /\ (s R_SP = sp) /\ (s V_MEM64 = mem) /\ (s R_X30 = raddr) /\ (s R_X0 = c)) (s := s).
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
    eapply islower_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
