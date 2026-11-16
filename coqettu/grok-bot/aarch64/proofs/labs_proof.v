(* labs -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/stdlib/labs.c:  return a>0 ? a : -a;  compiled to
       cmp x0,#0; cneg x0,x0,lt
   i.e. the 64-bit two's-complement negation when the argument is negative.

   SPECIFICATION (man 3 abs, Linux man-pages 6.9.1)
   ------------------------------------------------
     SYNOPSIS
            #include <stdlib.h>
            int abs(int j);
            long labs(long j);
            long long llabs(long long j);

     DESCRIPTION
            The abs() function computes the absolute value of the integer
            argument j.  The labs(), llabs(), and imaxabs() functions compute
            the absolute value of the argument j of the appropriate integer
            type for the function.

     RETURN VALUE
            Returns the absolute value of the integer argument, of the
            appropriate integer type for the function.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            labs at 0x5d388 (ELF vaddr); 0x15d388 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/labs_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = j (long); X30 = return address.
   Output:  At the RET (0x15d390): X0 = ofZ 64 (Z.abs (toZ 64 j)), i.e. the
            absolute value of j read as a signed 64-bit integer, reduced to
            64 bits (labs_spec).  For the most negative value (-2^63),
            where C leaves the result undefined, the machine result wraps
            to -2^63 itself (this is what the formula gives).  Memory, SP,
            X30 and the AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import labs_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem labs_nwc: ∀ s2 s1, labs_armv8 s1 = labs_armv8 s2.
Proof. reflexivity. Qed.

Theorem labs_welltyped: welltyped_prog arm8typctx labs_armv8.
Proof. Picinae_typecheck. Qed.

Theorem labs_preserves_memory:
  forall_endstates labs_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem labs_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates labs_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem labs_preserves_x30:
  forall_endstates labs_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

Definition labs_spec (c:N) : N := ofZ 64 (Z.abs (toZ 64 c)).

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15d388 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15d390 => Post 0 (s R_X0 = labs_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition labs_exits := make_exits 0 labs_armv8 invs.
  Definition labs_invs := make_invs 0 labs_armv8 invs.
End Invariants.


Theorem labs_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PROG: labs_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15d388, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (labs_invs sp mem raddr c) (labs_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=labs_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold labs_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply labs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  assert (C64 := MDL1 R_X0 64 eq_refl). rewrite X0 in C64. simpl in C64.
  repeat arm8_step; (split; [|repeat split; assumption]); unfold labs_spec;
  rewrite msub_0_r, N.mod_small in BC by exact C64;
  destruct (slt 64 c 0) eqn:S; cbn in BC; try discriminate; unfold slt in S; change (toZ 64 0) with 0%Z in S.
  - apply Z.ltb_lt in S. rewrite Z.abs_neq by lia.
    rewrite msub_sbop. f_equal.
  - apply Z.ltb_ge in S. rewrite Z.abs_eq by lia. rewrite ofZ_toZ. symmetry. apply N.mod_small, C64.
Qed.
