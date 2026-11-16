(* htonl -- musl i386, BSWAP implementation

   SEMANTICS
   ---------
   Reverse the four bytes of the input uint32_t, converting little-endian
   i386 host order to big-endian network order.

   SPECIFICATION (byteorder(3), Linux man-pages 6.9.1, 2024-05-02)
   ------------------------------------------------------------
     #include <arpa/inet.h>
     uint32_t htonl(uint32_t hostlong);
   Convert an unsigned 32-bit value from host to network byte order.
   Source: /usr/share/man/man3/htonl.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: htonl, ELF VA 0x58b92; Ghidra image base 0x10000,
           global entry 0x68b92, RET 0x68b98.
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
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits htonl_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition htonl_spec (c : N) : N := revbytes c 4.
Theorem htonl_spec_involutive : forall c,
  htonl_spec (htonl_spec c) = c.
Proof. intros. apply revbytes_involutive. Qed.

Definition htonl_invs (s0 : store) :=
  leaf_invs 0x68b92 0x68b98 s0 (htonl_spec (cdecl_arg s0)).
Definition htonl_exit := at_address 0x68b98.

Theorem htonl_nwc : forall s1 s2, htonl_i386 s1 = htonl_i386 s2.
Proof. reflexivity. Qed.

Theorem htonl_preserves_memory :
  forall_endstates htonl_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem htonl_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x68b92, s0)),
  satisfies_all htonl_i386 (htonl_invs s0) htonl_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold htonl_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold htonl_invs, leaf_invs, htonl_exit, at_address.
    all: repeat x86_step.
    all: try exact PRE.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, htonl_spec, cdecl_arg.
    all: psimpl.
    all: repeat split; try reflexivity.
    all: apply bswap_load32.
Qed.

Theorem htonl_correct :
  forall prog (EXT : htonl_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x68b92, s0)),
  satisfies_all prog (htonl_invs s0) htonl_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := htonl_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply htonl_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem htonl_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates htonl_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem htonl_returns :
  forall prog (EXT : htonl_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x68b98,s) = (Addr 0x68b92,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x68b98,s)::t))
    (UT : unterminated htonl_exit t),
  cdecl_returned s0 (htonl_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x68b92) (ret := 0x68b98).
  - discriminate.
  - apply EXT. reflexivity.
  - apply htonl_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
