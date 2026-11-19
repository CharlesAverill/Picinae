(* isalnum -- musl i386

   SEMANTICS
   ---------
   Classify the full 32-bit argument as an ASCII letter or decimal digit.
   Return exactly zero or one, preserving memory and the cdecl ABI frame.

   SPECIFICATION (isalnum(3), Linux man-pages 6.9.1, 2024-06-15)
   -------------------------------------------------------
     #include <ctype.h>
     int isalnum(int c);
   Return nonzero exactly for an ASCII letter or decimal digit; musl returns one.
   Source: /usr/share/man/man3/isalpha.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: isalnum, ELF VA 0x3ee61; global entry 0x4ee61, RET 0x4ee84.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The 32-bit argument is the word at entry ESP+4.
   Output: EAX is the classification result; memory, ESP, callee-saved registers
           and access permissions are preserved. RET pops the original address.
   Scope:  Partial correctness for all binary argument representations, stronger
           than C's unsigned-char/EOF domain. No locale table is consulted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits i386_ascii isalnum_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition isalnum_spec (c:N) : N := if ascii_alpha c || ascii_digit c then 1 else 0.
Definition isalnum_invs (s0 : store) :=
  leaf_invs 0x4ee61 0x4ee84 s0 (isalnum_spec (cdecl_arg s0)).
Definition isalnum_exit := at_address 0x4ee84.

Theorem isalnum_nwc : forall s1 s2, isalnum_i386 s1 = isalnum_i386 s2.
Proof. reflexivity. Qed.

Theorem isalnum_preserves_memory :
  forall_endstates isalnum_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isalnum_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4ee61, s0)),
  satisfies_all isalnum_i386 (isalnum_invs s0) isalnum_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold isalnum_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold isalnum_invs, leaf_invs, isalnum_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, isalnum_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: fold (cdecl_arg s0) in *.
    all: rewrite (ascii_lower_test (N.lor (cdecl_arg s0) 32)
      (or32_bound (cdecl_arg s0) ltac:(unfold cdecl_arg; apply getmem_bound))) in BC.
    all: unfold ascii_lower in BC.
    all: rewrite (alpha_fold (cdecl_arg s0)) in BC.
    all: destruct (ascii_alpha (cdecl_arg s0)) eqn:ALPHA; cbn in BC; try discriminate.
    all: cbn [orb].
    all: first [reflexivity|apply ascii_digit_test; unfold cdecl_arg; apply getmem_bound].
Qed.

Theorem isalnum_correct :
  forall prog (EXT : isalnum_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4ee61, s0)),
  satisfies_all prog (isalnum_invs s0) isalnum_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := isalnum_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply isalnum_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem isalnum_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates isalnum_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem isalnum_returns :
  forall prog (EXT : isalnum_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4ee84,s) = (Addr 0x4ee61,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4ee84,s)::t))
    (UT : unterminated isalnum_exit t),
  cdecl_returned s0 (isalnum_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4ee61) (ret := 0x4ee84).
  - discriminate.
  - apply EXT. reflexivity.
  - apply isalnum_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
