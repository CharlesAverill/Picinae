(* __strcasecmp_l -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64: a single tail branch to strcasecmp

   SEMANTICS
   ---------
   __strcasecmp_l is compiled to one instruction, b strcasecmp: the locale argument (if
   any) is ignored and the arguments are passed through unchanged, as in
   musl (the _l variants ignore their locale_t; iswblank is isblank;
   strcoll and wcscoll are strcmp and wcscmp in musl C locale handling).

   SPECIFICATION
   -------------
   Exactly the specification of strcasecmp (see proofs/strcasecmp_proof.v): the
   theorem below has the same hypotheses and the same invariant set as
   strcasecmp_partial_correctness, started at the entry of __strcasecmp_l; it is proved
   from that theorem with GrokTail.tailcall_satisfies_all.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            __strcasecmp_l at 0x5eb20 (ELF vaddr); 0x15eb20 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/__strcasecmp_l_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input/Output: as for strcasecmp; the program must contain both __strcasecmp_l and
            strcasecmp (and whatever strcasecmp itself calls).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import __strcasecmp_l_armv8 strcasecmp_armv8 tolower_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import strcasecmp_proof.
Import ARM8Notations.
Open Scope N.

Theorem __strcasecmp_l_nwc: ∀ s2 s1, __strcasecmp_l_armv8 s1 = __strcasecmp_l_armv8 s2.
Proof. reflexivity. Qed.

Theorem __strcasecmp_l_welltyped: welltyped_prog arm8typctx __strcasecmp_l_armv8.
Proof. Picinae_typecheck. Qed.

Theorem __strcasecmp_l_partial_correctness:
  ∀ prog s sp mem raddr p q x19 x20 x21 x29 Lp Lq t xs'
    (PW: __strcasecmp_l_armv8 ⊆2 prog) (P1: strcasecmp_armv8.strcasecmp_armv8 ⊆2 prog) (P0: tolower_armv8.tolower_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eb20, s))
    (PRE0: strcasecmp_pre sp mem p q Lp Lq) (MDL: models arm8typctx s) (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p) (X1: s R_X1 = q) (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p q x19 x20 x21 x29) (exits1 sp mem raddr p q x19 x20 x21 x29) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog _ _) with (a0 := 0x15eb20) (a1 := 0x15ea9c)
    (P := fun s => (strcasecmp_pre sp mem p q Lp Lq) /\ (models arm8typctx s) /\ (s R_SP = sp) /\ (s V_MEM64 = mem) /\ (s R_X30 = raddr) /\ (s R_X0 = p) /\ (s R_X1 = q) /\ (s R_X19 = x19) /\ (s R_X20 = x20) /\ (s R_X21 = x21) /\ (s R_X29 = x29)) (s := s).
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
    eapply strcasecmp_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
