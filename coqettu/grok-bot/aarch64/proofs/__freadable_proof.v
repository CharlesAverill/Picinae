(* __freadable -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl's C source is (essentially)

       int __freadable(FILE *f) { return !(f->flags & F_NORD); }  (F_NORD = 4; compiled as a 64-bit load of the first word, testing bit 2, which is bit 2 of byte 0)

   compiled to straight-line code without calls or stack use.

   SPECIFICATION
   -------------
   POSIX / Linux man-pages: __freadable returns 0 if F_NORD (bit 2) of the flags word at offset 0 is set, else 1 (musl representation; field offsets
   are those of musl's aarch64 structure layout, as used by the binary).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            __freadable at 0x5394c (ELF vaddr); 0x15394c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/__freadable_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x153958): s R_X0 = (if N.testbit (mem Ⓑ[a]) 2 then 0 else 1) /\ s V_MEM64 = mem
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory is unchanged; SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import __freadable_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem __freadable_nwc: ∀ s2 s1, __freadable_armv8 s1 = __freadable_armv8 s2.
Proof. reflexivity. Qed.

Theorem __freadable_welltyped: welltyped_prog arm8typctx __freadable_armv8.
Proof. Picinae_typecheck. Qed.

Theorem __freadable_preserves_memory:
  forall_endstates __freadable_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem __freadable_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates __freadable_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem __freadable_preserves_x30:
  forall_endstates __freadable_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition __freadable_post (s:store) :=
    s R_X0 = (if N.testbit (mem Ⓑ[a]) 2 then 0 else 1) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x15394c => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_X2 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x153958 => Post 0 (__freadable_post s)
    | _ => NoInv
    end.
  Definition __freadable_exits := make_exits 0 __freadable_armv8 invs.
  Definition __freadable_invs := make_invs 0 __freadable_armv8 invs.
End Invariants.

Theorem __freadable_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: __freadable_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15394c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c),
  satisfies_all prog (__freadable_invs sp mem raddr a b c) (__freadable_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=__freadable_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold __freadable_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply __freadable_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold __freadable_post; splits; try reflexivity; try assumption.
  all: apply bit_not.
Qed.
