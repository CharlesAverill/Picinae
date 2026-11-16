(* ntohl -- musl i386, BSWAP implementation

   SEMANTICS
   ---------
   Reverse the four bytes of the input uint32_t, converting big-endian
   network order to little-endian i386 host order.

   SPECIFICATION (byteorder(3), Linux man-pages 6.9.1, 2024-05-02)
   ------------------------------------------------------------
     #include <arpa/inet.h>
     uint32_t ntohl(uint32_t netlong);
   Convert an unsigned 32-bit value from network to host byte order.
   Source: /usr/share/man/man3/ntohl.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: ntohl, ELF VA 0x59ef7; Ghidra image base 0x10000,
           global entry 0x69ef7, RET 0x69efd.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the uint32_t argument
           is the little-endian word at ESP+4 in entry memory.
   Output: At RET, EAX = revbytes argument 4.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  Arbitrary containing program and
           arbitrary uint32_t argument.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits ntohl_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition ntohl_spec (c : N) : N := revbytes c 4.
Theorem ntohl_spec_involutive : forall c,
  ntohl_spec (ntohl_spec c) = c.
Proof. intros. apply revbytes_involutive. Qed.

Definition ntohl_invs (s0 : store) :=
  leaf_invs 0x69ef7 0x69efd s0 (ntohl_spec (cdecl_arg s0)).
Definition ntohl_exit := at_address 0x69efd.

Theorem ntohl_nwc : forall s1 s2, ntohl_i386 s1 = ntohl_i386 s2.
Proof. reflexivity. Qed.

Theorem ntohl_preserves_memory :
  forall_endstates ntohl_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ntohl_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x69ef7, s0)),
  satisfies_all ntohl_i386 (ntohl_invs s0) ntohl_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold ntohl_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold ntohl_invs, leaf_invs, ntohl_exit, at_address.
    all: repeat x86_step.
    all: try exact PRE.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, ntohl_spec, cdecl_arg.
    all: psimpl.
    all: repeat split; try reflexivity.
    all: apply bswap_load32.
Qed.

Theorem ntohl_correct :
  forall prog (EXT : ntohl_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x69ef7, s0)),
  satisfies_all prog (ntohl_invs s0) ntohl_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := ntohl_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply ntohl_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem ntohl_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates ntohl_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem ntohl_returns :
  forall prog (EXT : ntohl_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x69efd,s) = (Addr 0x69ef7,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x69efd,s)::t))
    (UT : unterminated ntohl_exit t),
  cdecl_returned s0 (ntohl_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x69ef7) (ret := 0x69efd).
  - discriminate.
  - apply EXT. reflexivity.
  - apply ntohl_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
