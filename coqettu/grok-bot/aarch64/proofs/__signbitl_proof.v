(* __signbitl -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl src/math/__signbitl.c (LDBL_MANT_DIG == 113):
       int __signbitl(long double x) { union ldshape u = {x}; return u.i.se >> 15; }
   compiled to: sub sp, sp, #16; str q0, [sp]; ldr x0, [sp, #8];
   add sp, sp, #16; lsr x0, x0, #48; lsr w0, w0, #15; ret.
   SPECIFICATION
   -------------
   Returns the sign bit of the IEEE binary128 long double x, which AAPCS64
   passes in q0.  Picinae models v0 as the low bits of the 256-bit R_Z0, so
   x = Z0 mod 2^128 and the result is bit 127 of Z0, written as
   ((Z0 >> 64) mod 2^64) >> 63 (the high 64-bit half, shifted by 63).
   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            __signbitl at 0x2c0fc (ELF vaddr); 0x12c0fc in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/__signbitl_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   R_Z0 = c (q0 = c mod 2^128 is x); X30 = return address raddr;
            SP = sp; mem = memory on entry (X0..X1 unconstrained).
   Output:  If execution reaches the RET: X0 = ((c >> 64) mod 2^64) >> 63
            (bit 127 of c, 0 or 1), SP = sp, X30 = raddr, and memory =
            mem with the 16 bytes of q0 stored at sp - 16 (its own stack
            slot below the entry SP; Ⓧ = 16-byte little-endian store).
            The other AAPCS64 callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import __signbitl_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem __signbitl_nwc: ∀ s2 s1, __signbitl_armv8 s1 = __signbitl_armv8 s2.
Proof. reflexivity. Qed.

Theorem __signbitl_welltyped: welltyped_prog arm8typctx __signbitl_armv8.
Proof. Picinae_typecheck. Qed.


Theorem __signbitl_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 ::
             R_X27 :: R_X28 :: R_X29 :: R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates __signbitl_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem __signbitl_preserves_x30:
  forall_endstates __signbitl_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition __signbitl_post (s:store) :=
    s R_X0 = ((c >> 64) mod 2^64 >> 63) /\ s V_MEM64 = (mem [Ⓧ sp ⊖ 16 := c]) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x12c0fc => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_Z0 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x12c114 => Post 0 (__signbitl_post s)
    | _ => NoInv
    end.
  Definition __signbitl_exits := make_exits 0 __signbitl_armv8 invs.
  Definition __signbitl_invs := make_invs 0 __signbitl_armv8 invs.
End Invariants.

Theorem __signbitl_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: __signbitl_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x12c0fc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_Z0 = c),
  satisfies_all prog (__signbitl_invs sp mem raddr a b c) (__signbitl_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=__signbitl_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold __signbitl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply __signbitl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold __signbitl_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
Qed.
