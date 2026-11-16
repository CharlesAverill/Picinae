(* div -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/stdlib/div.c:
       div_t div(int num, int den) { return (div_t){ num/den, num%den }; }
   compiled to  sdiv w2,w0,w1; mov w3,w0; mov x0,#0; bfxil x0,x2,#0,#32;
   msub w2,w2,w1,w3; bfi x0,x2,#32,#32; ret.
   The 8-byte struct {int quot; int rem;} is returned packed in X0:
   quot in bits 0..31, rem in bits 32..63.

   SPECIFICATION (man 3 div, Linux man-pages 6.9.1)
   ------------------------------------------------
     SYNOPSIS
            #include <stdlib.h>
            div_t div(int numerator, int denominator);
     DESCRIPTION
            The div() function computes the value numerator/denominator and
            returns the quotient and remainder in a structure named div_t that
            contains two integer members (in unspecified order) named quot and
            rem.  The quotient is rounded toward zero.  The result satisfies
            quot*denominator+rem = numerator.
   (C leaves the behaviour undefined if the denominator is 0 or the quotient
   is not representable; the theorem below still describes what this machine
   code does in those cases.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            div at 0x5d170 (ELF vaddr); 0x15d170 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/div_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = num, W1 = den (32-bit two's complement; upper halves of X0/X1
            ignored); X30 = return address.
   Output:  If execution reaches the RET (0x15d188):
              X0 = sdiv32 num den  OR  (srem32 num den << 32)   (lib/GrokDiv.v)
            where sdiv32 = 0 and srem32 = num mod 2^32 when den mod 2^32 = 0
            (aarch64 sdiv), otherwise the truncating 32-bit quotient and
            num - quot*den mod 2^32.
            div_semantics: if den <> 0 and not (num = INT_MIN and den = -1),
              toZ32 quot = Z.quot num den and toZ32 rem = Z.rem num den.
            Memory, SP, X30 and the AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import div_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokDiv.
Import ARM8Notations.
Open Scope N.

Theorem div_welltyped: welltyped_prog arm8typctx div_armv8.
Proof. Picinae_typecheck. Qed.

Theorem div_preserves_memory:
  forall_endstates div_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem div_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates div_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem div_preserves_x30:
  forall_endstates div_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15d170 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15d188 => Post 0 (s R_X0 = N.lor (sdiv32 c d) (N.shiftl (srem32 c d) 32) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition div_exits := make_exits 0 div_armv8 invs.
  Definition div_invs := make_invs 0 div_armv8 invs.
End Invariants.

Theorem div_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: div_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15d170, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (div_invs sp mem raddr c d) (div_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=div_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold div_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply div_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: unfold sdiv32, srem32; rewrite BC; rewrite ?N.shiftr_0_r, shl32_hi_mask.
  - rewrite N.lor_0_l. reflexivity.
  - unfold msub at 1. rewrite N.Div0.mod_mod. reflexivity.
Qed.

(* Meaning of the two 32-bit halves of X0 in terms of signed integers. *)
Corollary div_semantics:
  ∀ c d, toZ 32 d ≠ 0%Z -> ~ (toZ 32 c = (-2^31)%Z /\ toZ 32 d = (-1)%Z) ->
  toZ 32 (sdiv32 c d) = Z.quot (toZ 32 c) (toZ 32 d) /\
  toZ 32 (srem32 c d) = Z.rem (toZ 32 c) (toZ 32 d).
Proof. intros. apply sdiv32_srem32_semantics; assumption. Qed.
