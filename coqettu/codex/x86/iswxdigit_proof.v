(* iswxdigit -- musl i386 wide-character classification

   SEMANTICS / SPECIFICATION
   Return one exactly for a hexadecimal digit: U+0030..0039, U+0041..0046 or U+0061..0066, and zero otherwise.
   Source: /usr/share/man/man3/iswxdigit.3.gz, Linux man-pages 6.9.1
   (paraphrased). The exact binary predicate covers every wint_t bit pattern.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x3f5af; Ghidra image base 0x10000; global RET 0x4f5d0.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   The argument is the entry word at ESP+4. EAX is exactly zero or one.
   Memory, ESP, callee-saved registers and permissions are preserved.
   RET pops the original address and adds four to entry ESP.
   Scope: partial correctness for every 32-bit input (including WEOF),
   in any containing program. Concrete access success is not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits i386_ascii iswxdigit_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition iswxdigit_spec (c:N) : N := if ascii_digit c || ascii_hex_letter c then 1 else 0.
Definition iswxdigit_invs (s0 : store) :=
  leaf_invs 0x4f5af 0x4f5d0 s0 (iswxdigit_spec (cdecl_arg s0)).
Definition iswxdigit_exit := at_address 0x4f5d0.

Theorem iswxdigit_nwc : forall s1 s2, iswxdigit_i386 s1 = iswxdigit_i386 s2.
Proof. reflexivity. Qed.

Theorem iswxdigit_preserves_memory :
  forall_endstates iswxdigit_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem iswxdigit_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4f5af, s0)),
  satisfies_all iswxdigit_i386 (iswxdigit_invs s0) iswxdigit_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold iswxdigit_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold iswxdigit_invs, leaf_invs, iswxdigit_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, iswxdigit_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: fold (cdecl_arg s0) in *.
    all: rewrite (ascii_digit_test (cdecl_arg s0)
      ltac:(unfold cdecl_arg; apply getmem_bound)) in BC.
    all: destruct (ascii_digit (cdecl_arg s0)) eqn:DIGIT; cbn in BC; try discriminate.
    all: cbn [orb].
    all: first [reflexivity|apply ascii_hex_letter_test; unfold cdecl_arg; apply getmem_bound].
Qed.

Theorem iswxdigit_correct :
  forall prog (EXT : iswxdigit_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4f5af, s0)),
  satisfies_all prog (iswxdigit_invs s0) iswxdigit_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := iswxdigit_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply iswxdigit_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem iswxdigit_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates iswxdigit_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem iswxdigit_returns :
  forall prog (EXT : iswxdigit_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4f5d0,s) = (Addr 0x4f5af,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4f5d0,s)::t))
    (UT : unterminated iswxdigit_exit t),
  cdecl_returned s0 (iswxdigit_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4f5af) (ret := 0x4f5d0).
  - discriminate.
  - apply EXT. reflexivity.
  - apply iswxdigit_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
