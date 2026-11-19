(* creall -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl src/complex/creall.c:

       long double creall(long double complex z) { return creall(z); }

   compiled to a lone RET.  Under AAPCS64 a complex long double (IEEE binary128) argument is passed
   in v0 (real part) and v1 (imaginary part), and the long double (IEEE binary128) result is
   returned in v0, so returning without touching v0 returns the real part.

   SPECIFICATION
   -------------
   C11 7.3.9.6 / man 3 creall: returns the real part of z.  Picinae models the
   SIMD/FP register file as the 256-bit registers R_Z0..R_Z31; the argument
   real part and the result are both the low 128 bits of R_Z0
   (q0 = Z0 mod 2^128).  The theorem states R_Z0 is unchanged at the RET, i.e. the
   result equals the real part passed in.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            creall at 0x1aaf0 (ELF vaddr); 0x11aaf0 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/creall_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Input:   R_Z0 = z (v0; its low 128 bits are the real part).
   Output:  The entry instruction is the RET itself; at it (0x11aaf0): s R_Z0 = z /\ s V_MEM64 = (mem)
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory is unchanged; SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import creall_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem creall_nwc: ∀ s2 s1, creall_armv8 s1 = creall_armv8 s2.
Proof. reflexivity. Qed.

Theorem creall_welltyped: welltyped_prog arm8typctx creall_armv8.
Proof. Picinae_typecheck. Qed.

Theorem creall_preserves_memory:
  forall_endstates creall_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem creall_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates creall_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem creall_preserves_x30:
  forall_endstates creall_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c z : N).
  Definition creall_post (s:store) :=
    s R_Z0 = z /\ s V_MEM64 = (mem) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x11aaf0 => Post 0 (creall_post s)
    | _ => NoInv
    end.
  Definition creall_exits := make_exits 0 creall_armv8 invs.
  Definition creall_invs := make_invs 0 creall_armv8 invs.
End Invariants.

Theorem creall_partial_correctness:
  ∀ prog s sp mem raddr a b c z t xs'
    (PROG: creall_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11aaf0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c) (Z0: s R_Z0 = z),
  satisfies_all prog (creall_invs sp mem raddr z) (creall_exits sp mem raddr z) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=creall_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold creall_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 Z0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. unfold creall_post. repeat split; assumption.
  intros. destruct_inv 64 PRE.
Qed.
