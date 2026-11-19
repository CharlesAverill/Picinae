(* conjl -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl src/complex/conjl.c:
       long double complex conjl(long double complex z) { return CMPLXL(creall(z), -cimagl(z)); }
   compiled to: sub sp, sp, #32; str q1, [sp, #16]; copy the low 64 bits of
   the imaginary part to [sp], flip bit 63 of its high 64 bits (eor with
   0x8000000000000000) into [sp, #8]; ldr q1, [sp]; add sp, sp, #32; ret.
   SPECIFICATION
   -------------
   C11 7.3.9.4 / man 3 conjl: returns the complex conjugate of z (same real
   part, negated imaginary part).  AAPCS64 passes and returns the binary128
   real part in q0 and imaginary part in q1; Picinae models them as the low
   128 bits of R_Z0 and R_Z1.  Negating a binary128 flips its sign bit,
   bit 127, so the result is q0 unchanged and q1 = (b mod 2^128) XOR 2^127,
   written as the low half b mod 2^64 combined by OR with the high half
   ((b >> 64) XOR 2^63) shifted left 64, all mod 2^128.
   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            conjl at 0x1a854 (ELF vaddr); 0x11a854 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/conjl_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   R_Z0 = c (real part in q0), R_Z1 = b (imaginary part in q1);
            X30 = return address raddr; SP = sp; mem = memory on entry.
   Output:  If execution reaches the RET: R_Z1 = (b mod 2^64 .| ((b >> 64)
            .^ 2^63) << 64) mod 2^128, R_Z0 = c, X0 = (b >> 64) mod 2^64 .^ 2^63
            (scratch), SP = sp, X30 = raddr, and memory = mem with the
            writes to its own 32-byte stack frame below the entry SP
            (q1 at sp-16, then the two halves of the result at sp-32, sp-24).
            The other AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import conjl_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem conjl_nwc: ∀ s2 s1, conjl_armv8 s1 = conjl_armv8 s2.
Proof. reflexivity. Qed.

Theorem conjl_welltyped: welltyped_prog arm8typctx conjl_armv8.
Proof. Picinae_typecheck. Qed.


Theorem conjl_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 ::
             R_X27 :: R_X28 :: R_X29 :: R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates conjl_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem conjl_preserves_x30:
  forall_endstates conjl_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition conjl_post (s:store) :=
    s R_X0 = ((b >> 64) mod 2^64 .^ 2^63) /\ s R_Z1 = ((b mod 2^64 .| (b >> 64 .^ 2^63) << 64) mod 2^128) /\ s R_Z0 = c /\ s V_MEM64 = (mem [Ⓧ sp ⊖ 16 := b] [Ⓠ sp ⊖ 32 := b] [Ⓠ sp ⊖ 24 := b >> 64 .^ 2^63]) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x11a854 => Inv 0 (s R_X0 = a /\ s R_Z1 = b /\ s R_Z0 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11a878 => Post 0 (conjl_post s)
    | _ => NoInv
    end.
  Definition conjl_exits := make_exits 0 conjl_armv8 invs.
  Definition conjl_invs := make_invs 0 conjl_armv8 invs.
End Invariants.

Theorem conjl_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: conjl_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11a854, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_Z1 = b) (X2: s R_Z0 = c),
  satisfies_all prog (conjl_invs sp mem raddr a b c) (conjl_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=conjl_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold conjl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply conjl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold conjl_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
Qed.
