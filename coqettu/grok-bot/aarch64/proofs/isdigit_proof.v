(* isdigit -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/ctype/isdigit.c:
       int isdigit(int c) { return (unsigned)c-'0' < 10; }
   compiled to  sub w0,w0,#lo; cmp w0,#k; cset w0,ls; ret  with
   lo = 0x30, k = 9 (cset ls = unsigned "lower or same").

   SPECIFICATION (man 3 isdigit, Linux man-pages 6.9.1, C/POSIX locale)
   -------------------------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int isdigit(int c);
     DESCRIPTION
            These functions check whether c, which must have the value of an
            unsigned char or EOF, falls into a certain character class
            according to the specified locale.
            isdigit()
                   checks for a digit (0 through 9).
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
            isdigit at 0x1ee64 (ELF vaddr); 0x11ee64 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/isdigit_armv8.v.
            (Generated from tools/ctype_template.v by tools/gen_ctype.py.)
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = c (X0 = c; only c mod 2^32 is used); X30 = return address.
   Output:  If execution reaches the RET (0x11ee70): X0 = 1 if
            48 <= c mod 2^32 <= 57 (0x30..0x39), else X0 = 0; this holds for
            every 32-bit input (EOF = -1 gives 0).  Memory, SP, X30 and the
            AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import isdigit_armv8.
From Grok.lib Require Import GrokCommon GrokCtype.
Import ARM8Notations.
Open Scope N.

Theorem isdigit_welltyped: welltyped_prog arm8typctx isdigit_armv8.
Proof. Picinae_typecheck. Qed.

Theorem isdigit_preserves_memory:
  forall_endstates isdigit_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isdigit_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates isdigit_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem isdigit_preserves_x30:
  forall_endstates isdigit_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition isdigit_spec (c:N) : N :=
  let c32 := c mod 2^32 in if (48 <=? c32) && (c32 <=? 57) then 1 else 0.

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11ee64 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11ee70 => Post 0 (s R_X0 = isdigit_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition isdigit_exits := make_exits 0 isdigit_armv8 invs.
  Definition isdigit_invs := make_invs 0 isdigit_armv8 invs.
End Invariants.

Theorem isdigit_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PROG: isdigit_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee64, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (isdigit_invs sp mem raddr c) (isdigit_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=isdigit_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold isdigit_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isdigit_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  split; [|repeat split; assumption].
  pose proof (ls_test c 48 9 eq_refl eq_refl) as LT. rewrite ?msub_0_r in LT. exact LT.
Qed.
