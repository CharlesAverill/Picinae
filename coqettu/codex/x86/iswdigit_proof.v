(* iswdigit -- musl i386 wide-character classification

   SEMANTICS / SPECIFICATION
   Return one exactly for a decimal digit: U+0030 through U+0039, and zero otherwise.
   Source: /usr/share/man/man3/iswdigit.3.gz, Linux man-pages 6.9.1
   (paraphrased). The exact binary predicate covers every wint_t bit pattern.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x3f355; Ghidra image base 0x10000; global RET 0x4f365.
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
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits iswdigit_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition iswdigit_spec (c : N) : N :=
  if (48 <=? c) && (c <=? 57) then 1 else 0.
Definition iswdigit_invs (s0 : store) :=
  leaf_invs 0x4f355 0x4f365 s0 (iswdigit_spec (cdecl_arg s0)).
Definition iswdigit_exit := at_address 0x4f365.

Theorem iswdigit_nwc : forall s1 s2, iswdigit_i386 s1 = iswdigit_i386 s2.
Proof. reflexivity. Qed.

Theorem iswdigit_preserves_memory :
  forall_endstates iswdigit_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem iswdigit_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4f355, s0)),
  satisfies_all iswdigit_i386 (iswdigit_invs s0) iswdigit_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold iswdigit_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold iswdigit_invs, leaf_invs, iswdigit_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, iswdigit_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: apply (classify_interval (cdecl_arg s0) 48 57);
      [unfold cdecl_arg; apply getmem_bound | lia | lia].
Qed.

Theorem iswdigit_correct :
  forall prog (EXT : iswdigit_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4f355, s0)),
  satisfies_all prog (iswdigit_invs s0) iswdigit_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := iswdigit_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply iswdigit_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem iswdigit_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates iswdigit_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem iswdigit_returns :
  forall prog (EXT : iswdigit_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4f365,s) = (Addr 0x4f355,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4f365,s)::t))
    (UT : unterminated iswdigit_exit t),
  cdecl_returned s0 (iswdigit_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4f355) (ret := 0x4f365).
  - discriminate.
  - apply EXT. reflexivity.
  - apply iswdigit_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
