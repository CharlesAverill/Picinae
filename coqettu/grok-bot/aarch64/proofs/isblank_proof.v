(* isblank -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/ctype/isblank.c:
       int isblank(int c) { return (c == ' ' || c == '\t'); }
   compiled to  cmp w0,#0x20; ccmp w0,#9,#4,ne; cset w0,eq; ret
   (the ccmp is stepped with grok_step from lib/GrokStep.v).

   SPECIFICATION (man 3 isblank, Linux man-pages 6.9.1, C/POSIX locale)
   -------------------------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int isblank(int c);
     DESCRIPTION
            These functions check whether c, which must have the value of an
            unsigned char or EOF, falls into a certain character class
            according to the specified locale.
            isblank()
                   checks for a blank character; that is, a space or a tab.
     RETURN VALUE
            The values returned are nonzero if the character c falls into
            the tested class, and zero if not.
   (musl supports only the C/POSIX ctype classes, i.e. ASCII.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            isblank at 0x1ee3c (ELF vaddr); 0x11ee3c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/isblank_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = c (X0 = c; only c mod 2^32 is used); X30 = return address.
   Output:  If execution reaches the RET (0x11ee48): X0 = 1 if c mod 2^32 is 0x20 or 0x09, else X0 = 0;
            this holds for every 32-bit input (EOF = -1 gives 0).  Memory, SP,
            X30 and the AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import isblank_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCtype.
Import ARM8Notations.
Open Scope N.

Theorem isblank_welltyped: welltyped_prog arm8typctx isblank_armv8.
Proof. Picinae_typecheck. Qed.

Theorem isblank_preserves_memory:
  forall_endstates isblank_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isblank_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates isblank_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem isblank_preserves_x30:
  forall_endstates isblank_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition isblank_spec (c:N) : N := let x := c mod 2^32 in if (x =? 32) || (x =? 9) then 1 else 0.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11ee3c => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11ee48 => Post 0 (s R_X0 = isblank_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition isblank_exits := make_exits 0 isblank_armv8 invs.
  Definition isblank_invs := make_invs 0 isblank_armv8 invs.
End Invariants.

Theorem isblank_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: isblank_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee3c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (isblank_invs sp mem raddr c d) (isblank_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=isblank_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold isblank_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isblank_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat grok_step.
  all: splits; try reflexivity; try assumption.
  all: unfold isblank_spec; cbv zeta.
  all: first [apply N.eqb_eq in BC | apply N.eqb_neq in BC].
  all: repeat match goal with
         | |- context [?a <=? ?b] => destruct (N.leb_spec a b)
         | |- context [?a <? ?b] => destruct (N.ltb_spec a b)
         | |- context [?a =? ?b] => destruct (N.eqb_spec a b) end.
  all: simpl; try reflexivity; lia.
Qed.
