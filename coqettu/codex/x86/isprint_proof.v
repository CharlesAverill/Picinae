(* isprint -- musl i386

   SEMANTICS
   ---------
   Return 1 exactly for unsigned argument representations in [32,126],
   and 0 otherwise. This also describes negative C int representations.

   SPECIFICATION (isprint(3), Linux man-pages 6.9.1, 2024-06-15)
   ----------------------------------------------------------
     #include <ctype.h>
     int isprint(int c);
   Return nonzero exactly for a printable ASCII character; musl returns 1.
   Source: /usr/share/man/man3/isprint.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: isprint, ELF VA 0x3efce; Ghidra image base 0x10000,
           global entry 0x4efce, RET 0x4efde.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the 32-bit argument is
           the little-endian word at ESP+4 in entry memory.
   Output: At RET, EAX = 1 if 32 <= argument <= 126, and 0 otherwise.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  The containing program may extend
           the lifted function arbitrarily.  No argument-value restriction.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits isprint_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition isprint_spec (c : N) : N :=
  if (32 <=? c) && (c <=? 126) then 1 else 0.
Definition isprint_invs (s0 : store) :=
  leaf_invs 0x4efce 0x4efde s0 (isprint_spec (cdecl_arg s0)).
Definition isprint_exit := at_address 0x4efde.

Theorem isprint_nwc : forall s1 s2, isprint_i386 s1 = isprint_i386 s2.
Proof. reflexivity. Qed.

Theorem isprint_preserves_memory :
  forall_endstates isprint_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isprint_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4efce, s0)),
  satisfies_all isprint_i386 (isprint_invs s0) isprint_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold isprint_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold isprint_invs, leaf_invs, isprint_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, isprint_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: apply (classify_interval (cdecl_arg s0) 32 126);
      [unfold cdecl_arg; apply getmem_bound | lia | lia].
Qed.

Theorem isprint_correct :
  forall prog (EXT : isprint_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4efce, s0)),
  satisfies_all prog (isprint_invs s0) isprint_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := isprint_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply isprint_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem isprint_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates isprint_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem isprint_returns :
  forall prog (EXT : isprint_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4efde,s) = (Addr 0x4efce,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4efde,s)::t))
    (UT : unterminated isprint_exit t),
  cdecl_returned s0 (isprint_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4efce) (ret := 0x4efde).
  - discriminate.
  - apply EXT. reflexivity.
  - apply isprint_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
