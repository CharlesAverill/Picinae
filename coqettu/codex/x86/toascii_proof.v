(* toascii -- musl i386

   SEMANTICS
   ---------
   Clear all but the low seven bits of the argument.  This applies to every
   32-bit int representation, including negative C int arguments.

   SPECIFICATION (toascii(3), Linux man-pages 6.9.1, 2024-05-02)
   ----------------------------------------------------------
     #include <ctype.h>
     int toascii(int c);
   Return the converted 7-bit ASCII value (the argument modulo 128).
   Source: /usr/share/man/man3/toascii.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: toascii, ELF VA 0x3f62d; Ghidra image base 0x10000,
           global entry 0x4f62d, RET 0x4f634.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the 32-bit argument is
           the little-endian word at ESP+4 in entry memory.
   Output: At RET, EAX = argument mod 128.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  The containing program may extend
           the lifted function arbitrarily.  No argument-value restriction.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common toascii_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition toascii_spec (c : N) : N := c mod 128.
Theorem toascii_spec_range : forall c, toascii_spec c < 128.
Proof. intros. apply (mp2_mod_lt c 7). Qed.

Theorem toascii_spec_idempotent : forall c,
  toascii_spec (toascii_spec c) = toascii_spec c.
Proof. intros. unfold toascii_spec. apply N.Div0.mod_mod. Qed.

Definition toascii_invs (s0 : store) :=
  leaf_invs 0x4f62d 0x4f634 s0 (toascii_spec (cdecl_arg s0)).
Definition toascii_exit := at_address 0x4f634.

Theorem toascii_nwc : forall s1 s2, toascii_i386 s1 = toascii_i386 s2.
Proof. reflexivity. Qed.

Theorem toascii_preserves_memory :
  forall_endstates toascii_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem toascii_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4f62d, s0)),
  satisfies_all toascii_i386 (toascii_invs s0) toascii_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold toascii_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold toascii_invs, leaf_invs, toascii_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, toascii_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
Qed.

Theorem toascii_correct :
  forall prog (EXT : toascii_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4f62d, s0)),
  satisfies_all prog (toascii_invs s0) toascii_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := toascii_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply toascii_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem toascii_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates toascii_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem toascii_returns :
  forall prog (EXT : toascii_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4f634,s) = (Addr 0x4f62d,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4f634,s)::t))
    (UT : unterminated toascii_exit t),
  cdecl_returned s0 (toascii_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4f62d) (ret := 0x4f634).
  - discriminate.
  - apply EXT. reflexivity.
  - apply toascii_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
