(* ldiv -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/stdlib/ldiv.c:
       ldiv_t ldiv(long num, long den) { return (ldiv_t){ num/den, num%den }; }
   compiled to  mov x2,x0; sdiv x0,x0,x1; msub x1,x0,x1,x2; ret.
   The 16-byte struct {quot; rem} is returned in X0 (quot) and X1 (rem).

   SPECIFICATION (man 3 div, Linux man-pages 6.9.1)
   ------------------------------------------------
     SYNOPSIS
            #include <stdlib.h>
            ldiv_t ldiv(long numerator, long denominator);
     DESCRIPTION
            The div() function computes the value numerator/denominator and
            returns the quotient and remainder in a structure named div_t that
            contains two integer members (in unspecified order) named quot and
            rem.  The quotient is rounded toward zero.  The result satisfies
            quot*denominator+rem = numerator.
            The ldiv(), lldiv(), and imaxdiv() functions do the same, dividing
            numbers of the indicated type and returning the result in a
            structure of the indicated name, in all cases with fields quot and
            rem of the same type as the function arguments.
   (C leaves the behaviour undefined if the denominator is 0 or the quotient
   is not representable; the theorem below still describes what this machine
   code does in those cases.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ldiv at 0x5d394 (ELF vaddr); 0x15d394 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/ldiv_armv8.v.
            (Generated from tools/div_template.v by tools/gen_div.py.)
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = num, X1 = den (64-bit two's complement); X30 = return address.
   Output:  If execution reaches the RET (0x15d3a0):
              X0 = sdiv64 num den, X1 = srem64 num den   (lib/GrokDiv.v), i.e.
              X0 = 0 and X1 = num when den = 0 (aarch64 sdiv), and otherwise
              X0 = the 64-bit truncating quotient, X1 = num - X0*den mod 2^64.
            ldiv_semantics: if den <> 0 and not (num = INT64_MIN and den = -1),
              toZ X0 = Z.quot num den and toZ X1 = Z.rem num den, so
              quot*den + rem = num with the quotient rounded toward zero.
            Memory, SP, X30 and the AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ldiv_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokDiv.
Import ARM8Notations.
Open Scope N.

Theorem ldiv_welltyped: welltyped_prog arm8typctx ldiv_armv8.
Proof. Picinae_typecheck. Qed.

Theorem ldiv_preserves_memory:
  forall_endstates ldiv_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ldiv_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates ldiv_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem ldiv_preserves_x30:
  forall_endstates ldiv_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15d394 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15d3a0 => Post 0 (s R_X0 = sdiv64 c d /\ s R_X1 = srem64 c d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ldiv_exits := make_exits 0 ldiv_armv8 invs.
  Definition ldiv_invs := make_invs 0 ldiv_armv8 invs.
End Invariants.

Theorem ldiv_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: ldiv_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15d394, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (ldiv_invs sp mem raddr c d) (ldiv_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ldiv_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ldiv_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ldiv_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: unfold srem64, sdiv64; rewrite BC; splits; try reflexivity; try assumption.
  pose proof (MDL1 R_X0 64 eq_refl) as C64. rewrite X0 in C64.
  rewrite N.mul_0_l, msub_0_r. symmetry. apply N.mod_small. exact C64.
Qed.

(* Meaning of the returned pair in terms of signed integers. *)
Corollary ldiv_semantics:
  ∀ c d, toZ 64 d ≠ 0%Z -> ~ (toZ 64 c = (-2^63)%Z /\ toZ 64 d = (-1)%Z) ->
  toZ 64 (sdiv64 c d) = Z.quot (toZ 64 c) (toZ 64 d) /\
  toZ 64 (srem64 c d) = Z.rem (toZ 64 c) (toZ 64 d).
Proof. intros. apply sdiv64_srem64_semantics; assumption. Qed.
