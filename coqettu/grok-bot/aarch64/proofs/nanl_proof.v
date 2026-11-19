(* nanl -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl src/math/nanl.c:
       long double nanl(const char *s) { return NAN; }
   compiled to: adrp x0, ...; add x0, x0, #0x320; ldr q0, [x0]; ret,
   loading the quiet-NaN long double constant from read-only data at
   ELF 0x6e320 (Ghidra 0x16e320).
   SPECIFICATION
   -------------
   C11 7.12.11.2 / man 3 nanl: returns a quiet NaN (musl ignores the
   argument string).  The result is the 16-byte constant read from memory at
   the constant address; in the loaded binary those read-only bytes are the
   binary128 quiet NaN.  Picinae models q0 as the low 128 bits of R_Z0; the
   lifted ldr q0 sets the whole R_Z0 to the loaded 128-bit value.
   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            nanl at 0x37d6c (ELF vaddr); 0x137d6c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/nanl_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (ignored); X30 = return address raddr; SP = sp;
            mem = memory on entry.
   Output:  If execution reaches the RET: X0 = 0x16e320, R_Z0 =
            mem Ⓧ[0x16e320] (16-byte little-endian read), memory unchanged,
            SP = sp, X30 = raddr; callee-saved registers unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import nanl_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem nanl_nwc: ∀ s2 s1, nanl_armv8 s1 = nanl_armv8 s2.
Proof. reflexivity. Qed.

Theorem nanl_welltyped: welltyped_prog arm8typctx nanl_armv8.
Proof. Picinae_typecheck. Qed.

Theorem nanl_preserves_memory:
  forall_endstates nanl_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem nanl_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates nanl_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem nanl_preserves_x30:
  forall_endstates nanl_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition nanl_post (s:store) :=
    s R_X0 = (0x16e320) /\ s R_Z0 = mem Ⓧ[0x16e320] /\ s V_MEM64 = (mem) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x137d6c => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_Z0 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x137d78 => Post 0 (nanl_post s)
    | _ => NoInv
    end.
  Definition nanl_exits := make_exits 0 nanl_armv8 invs.
  Definition nanl_invs := make_invs 0 nanl_armv8 invs.
End Invariants.

Theorem nanl_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: nanl_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x137d6c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_Z0 = c),
  satisfies_all prog (nanl_invs sp mem raddr a b c) (nanl_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=nanl_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold nanl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply nanl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold nanl_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
Qed.
