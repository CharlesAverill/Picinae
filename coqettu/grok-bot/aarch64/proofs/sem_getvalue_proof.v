(* sem_getvalue -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl's C source is (essentially)

       int sem_getvalue(sem_t *restrict sem, int *restrict valp) { a_barrier(); int val = sem->__val[0]; *valp = val & SEM_VALUE_MAX; return 0; }  (SEM_VALUE_MAX = 0x7fffffff)

   compiled to straight-line code without calls or stack use.

   SPECIFICATION
   -------------
   POSIX / Linux man-pages: sem_getvalue stores the semaphore count AND 0x7fffffff to *valp and returns 0 (musl representation; field offsets
   are those of musl's aarch64 structure layout, as used by the binary).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            sem_getvalue at 0x64720 (ELF vaddr); 0x164720 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/sem_getvalue_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x164730): s R_X0 = (0) /\ s V_MEM64 = mem [Ⓓ b := mem Ⓓ[a] .& 2147483647]
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory changes exactly as stated (no other byte changes); SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import sem_getvalue_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem sem_getvalue_nwc: ∀ s2 s1, sem_getvalue_armv8 s1 = sem_getvalue_armv8 s2.
Proof. reflexivity. Qed.

Theorem sem_getvalue_welltyped: welltyped_prog arm8typctx sem_getvalue_armv8.
Proof. Picinae_typecheck. Qed.


Theorem sem_getvalue_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates sem_getvalue_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem sem_getvalue_preserves_x30:
  forall_endstates sem_getvalue_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition sem_getvalue_post (s:store) :=
    s R_X0 = (0) /\ s V_MEM64 = mem [Ⓓ b := mem Ⓓ[a] .& 2147483647] /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x164720 => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_X2 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x164730 => Post 0 (sem_getvalue_post s)
    | _ => NoInv
    end.
  Definition sem_getvalue_exits := make_exits 0 sem_getvalue_armv8 invs.
  Definition sem_getvalue_invs := make_invs 0 sem_getvalue_armv8 invs.
End Invariants.

Theorem sem_getvalue_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: sem_getvalue_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x164720, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c),
  satisfies_all prog (sem_getvalue_invs sp mem raddr a b c) (sem_getvalue_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=sem_getvalue_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold sem_getvalue_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sem_getvalue_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold sem_getvalue_post; splits; try reflexivity; try assumption.

Qed.
