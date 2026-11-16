(* sigemptyset -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/signal/sigemptyset.c (64-bit long, _NSIG = 65 on aarch64):
       int sigemptyset(sigset_t *set) { set->__bits[0] = 0; return 0; }
   (the stores to __bits[1] and beyond are compiled out because _NSIG <= 65)
   compiled to  str xzr,[x0]; mov w0,#0; ret.
   All 64 signal bits are cleared.

   SPECIFICATION (man 3 sigsetops, Linux man-pages 6.9.1)
   ------------------------------------------------------
     SYNOPSIS
            #include <signal.h>
            int sigemptyset(sigset_t *set);
     DESCRIPTION
            These functions allow the manipulation of POSIX signal sets.
            sigemptyset() initializes the signal set given by set to empty,
            with all signals excluded from the set.
     RETURN VALUE
            sigemptyset(), sigfillset(), sigaddset(), and sigdelset() return 0
            on success and -1 on error.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            sigemptyset at 0x5221c (ELF vaddr); 0x15221c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/sigemptyset_armv8.v.
            (Generated from tools/sigset_template.v by tools/gen_sigset.py.)
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = set (any address); X30 = return address.
   Output:  If execution reaches the RET (0x152224): X0 = 0 and memory is the
            entry memory with the 8 little-endian bytes at set replaced by
            0 (signal n is member iff bit n-1 of that word is set); no
            other byte changes.  SP, X30 and the AAPCS64 callee-saved
            registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import sigemptyset_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Theorem sigemptyset_welltyped: welltyped_prog arm8typctx sigemptyset_armv8.
Proof. Picinae_typecheck. Qed.

Theorem sigemptyset_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates sigemptyset_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem sigemptyset_preserves_x30:
  forall_endstates sigemptyset_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr p : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15221c => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x152224 => Post 0 (s R_X0 = 0 /\ s V_MEM64 = setmem 64 LittleE 8 mem p 0 /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition sigemptyset_exits := make_exits 0 sigemptyset_armv8 invs.
  Definition sigemptyset_invs := make_invs 0 sigemptyset_armv8 invs.
End Invariants.

Theorem sigemptyset_partial_correctness:
  ∀ prog s sp mem raddr p t xs'
    (PROG: sigemptyset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15221c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p),
  satisfies_all prog (sigemptyset_invs sp mem raddr p) (sigemptyset_exits sp mem raddr p) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=sigemptyset_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold sigemptyset_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigemptyset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
Qed.
