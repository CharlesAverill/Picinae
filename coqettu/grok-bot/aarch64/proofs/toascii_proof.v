(* toascii -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/ctype/toascii.c:
       int toascii(int c) { return c & 0x7f; }
   compiled to  and w0,w0,#0x7f; ret.

   SPECIFICATION (man 3 toascii, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int toascii(int c);
     DESCRIPTION
            toascii() converts c to a 7-bit unsigned char value that fits
            into the ASCII character set, by clearing the high-order bits.
     RETURN VALUE
            The value returned is that of the converted character.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            toascii at 0x1f2c8 (ELF vaddr); 0x11f2c8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/toascii_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = c (X0 = c; only the low 7 bits matter); X30 = return address.
   Output:  If execution reaches the RET (0x11f2cc): X0 = c mod 128 (the low
            7 bits of c, zero-extended to 64 bits).  Memory, SP, X30 and the
            AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import toascii_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Theorem toascii_welltyped: welltyped_prog arm8typctx toascii_armv8.
Proof. Picinae_typecheck. Qed.

Theorem toascii_preserves_memory:
  forall_endstates toascii_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem toascii_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates toascii_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem toascii_preserves_x30:
  forall_endstates toascii_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11f2c8 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11f2cc => Post 0 (s R_X0 = c mod 128 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition toascii_exits := make_exits 0 toascii_armv8 invs.
  Definition toascii_invs := make_invs 0 toascii_armv8 invs.
End Invariants.

Theorem toascii_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PROG: toascii_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11f2c8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (toascii_invs sp mem raddr c) (toascii_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=toascii_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold toascii_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply toascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  split; [|repeat split; assumption].
  reflexivity.
Qed.
