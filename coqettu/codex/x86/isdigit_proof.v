(* isdigit -- musl i386

   SEMANTICS
   ---------
   Return 1 exactly for unsigned argument representations in [48,57],
   and 0 otherwise. This also describes negative C int representations.

   SPECIFICATION (isdigit(3), Linux man-pages 6.9.1, 2024-06-15)
   ----------------------------------------------------------
     #include <ctype.h>
     int isdigit(int c);
   Return nonzero exactly for a decimal digit; musl returns 1.
   Source: /usr/share/man/man3/isdigit.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: isdigit, ELF VA 0x3ef44; Ghidra image base 0x10000,
           global entry 0x4ef44, RET 0x4ef54.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the 32-bit argument is
           the little-endian word at ESP+4 in entry memory.
   Output: At RET, EAX = 1 if 48 <= argument <= 57, and 0 otherwise.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  The containing program may extend
           the lifted function arbitrarily.  No argument-value restriction.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits isdigit_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition isdigit_spec (c : N) : N :=
  if (48 <=? c) && (c <=? 57) then 1 else 0.
Definition isdigit_invs (s0 : store) :=
  leaf_invs 0x4ef44 0x4ef54 s0 (isdigit_spec (cdecl_arg s0)).
Definition isdigit_exit := at_address 0x4ef54.

Theorem isdigit_nwc : forall s1 s2, isdigit_i386 s1 = isdigit_i386 s2.
Proof. reflexivity. Qed.

Theorem isdigit_preserves_memory :
  forall_endstates isdigit_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isdigit_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4ef44, s0)),
  satisfies_all isdigit_i386 (isdigit_invs s0) isdigit_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold isdigit_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold isdigit_invs, leaf_invs, isdigit_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, isdigit_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: apply (classify_interval (cdecl_arg s0) 48 57);
      [unfold cdecl_arg; apply getmem_bound | lia | lia].
Qed.

Theorem isdigit_correct :
  forall prog (EXT : isdigit_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4ef44, s0)),
  satisfies_all prog (isdigit_invs s0) isdigit_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := isdigit_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply isdigit_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem isdigit_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates isdigit_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem isdigit_returns :
  forall prog (EXT : isdigit_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4ef54,s) = (Addr 0x4ef44,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4ef54,s)::t))
    (UT : unterminated isdigit_exit t),
  cdecl_returned s0 (isdigit_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4ef44) (ret := 0x4ef54).
  - discriminate.
  - apply EXT. reflexivity.
  - apply isdigit_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
