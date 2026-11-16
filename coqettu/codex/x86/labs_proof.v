(* labs -- musl i386

   SEMANTICS
   ---------
   Return the two's-complement absolute value of a 32-bit signed long.
   The binary also maps INT_MIN to the INT_MIN bit pattern; the portable C
   specification leaves that unrepresentable absolute value undefined.

   SPECIFICATION (labs(3), Linux man-pages 6.9.1, local manual)
   --------------------------------------------------------
     #include <stdlib.h>
     long labs(long j);
   Return the absolute value, provided it is representable as a long.
   Source: /usr/share/man/man3/labs.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: labs, ELF VA 0x65270; Ghidra image base 0x10000,
           global entry 0x75270, RET 0x75279.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the 32-bit argument is
           the little-endian word at ESP+4 in entry memory.
   Output: At RET, EAX = argument if below 2^31, else 2^32-argument.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  The containing program may extend
           the lifted function arbitrarily.  No argument-value restriction.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits labs_i386.
From Stdlib Require Import NArith ZArith.
Import X86Notations.
Open Scope N.

Definition labs_spec (c : N) : N :=
  if c <? 2^31 then c else 2^32 - c.
Theorem labs_spec_signed : forall c,
  c < 2^32 -> c <> 2^31 ->
  toZ 32 (labs_spec c) = Z.abs (toZ 32 c).
Proof. apply abs_word_signed. Qed.

Definition labs_invs (s0 : store) :=
  leaf_invs 0x75270 0x75279 s0 (labs_spec (cdecl_arg s0)).
Definition labs_exit := at_address 0x75279.

Theorem labs_nwc : forall s1 s2, labs_i386 s1 = labs_i386 s2.
Proof. reflexivity. Qed.

Theorem labs_preserves_memory :
  forall_endstates labs_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem labs_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x75270, s0)),
  satisfies_all labs_i386 (labs_invs s0) labs_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold labs_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold labs_invs, leaf_invs, labs_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, labs_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: apply abs_branchless, getmem_bound.
Qed.

Theorem labs_correct :
  forall prog (EXT : labs_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x75270, s0)),
  satisfies_all prog (labs_invs s0) labs_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := labs_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply labs_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem labs_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates labs_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem labs_returns :
  forall prog (EXT : labs_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x75279,s) = (Addr 0x75270,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x75279,s)::t))
    (UT : unterminated labs_exit t),
  cdecl_returned s0 (labs_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x75270) (ret := 0x75279).
  - discriminate.
  - apply EXT. reflexivity.
  - apply labs_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
