(* htons -- musl i386, ROL AX implementation

   SEMANTICS
   ---------
   Reverse the two low bytes of the input uint16_t, converting little-endian
   i386 host order to big-endian network order.

   SPECIFICATION (byteorder(3), Linux man-pages 6.9.1, 2024-05-02)
   ------------------------------------------------------------
     #include <arpa/inet.h>
     uint16_t htons(uint16_t hostlong);
   Convert an unsigned 16-bit value from host to network byte order.
   Source: /usr/share/man/man3/htons.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: htons, ELF VA 0x58b99; Ghidra image base 0x10000,
           global entry 0x68b99, RET 0x68ba1.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  ESP points at the saved return address; the uint16_t argument is in the low 16 bits
           of the 32-bit slot at ESP+4. The upper 16 bits are arbitrary.
   Output: High 16 EAX bits preserve the argument-slot high bits.
           At RET, EAX = revbytes argument 2.  ESP, memory, EBX, ESI, EDI,
           EBP and access permissions equal their entry values.
   Scope:  Partial correctness at RET and after executing RET.  The
           *_returns theorem pops the saved return address and adds 4 to ESP.  Arbitrary containing program and
           arbitrary uint16_t argument.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits htons_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition htons_spec (c : N) : N := revbytes c 2.
Theorem htons_spec_involutive : forall c,
  htons_spec (htons_spec c) = c.
Proof. intros. apply revbytes_involutive. Qed.

Definition htons_invs (s0 : store) :=
  leaf_invs 0x68b99 0x68ba1 s0 (htons_spec (cdecl_arg s0)).
Definition htons_exit := at_address 0x68ba1.

Theorem htons_nwc : forall s1 s2, htons_i386 s1 = htons_i386 s2.
Proof. reflexivity. Qed.

Theorem htons_preserves_memory :
  forall_endstates htons_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem htons_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x68b99, s0)),
  satisfies_all htons_i386 (htons_invs s0) htons_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold htons_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold htons_invs, leaf_invs, htons_exit, at_address.
    all: repeat x86_step.
    all: try exact PRE.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, htons_spec, cdecl_arg.
    all: psimpl.
    all: repeat split; try reflexivity.
    all: apply bswap_load16.
Qed.

Theorem htons_correct :
  forall prog (EXT : htons_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x68b99, s0)),
  satisfies_all prog (htons_invs s0) htons_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := htons_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply htons_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem htons_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates htons_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem htons_returns :
  forall prog (EXT : htons_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x68ba1,s) = (Addr 0x68b99,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x68ba1,s)::t))
    (UT : unterminated htons_exit t),
  cdecl_returned s0 (htons_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x68b99) (ret := 0x68ba1).
  - discriminate.
  - apply EXT. reflexivity.
  - apply htons_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
