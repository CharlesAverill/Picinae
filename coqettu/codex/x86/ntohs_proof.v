(* ntohs -- musl i386, ROL AX implementation

   SEMANTICS
   ---------
   Reverse the two low bytes of the input uint16_t, converting big-endian
   network order to little-endian i386 host order.

   SPECIFICATION (byteorder(3), Linux man-pages 6.9.1, 2024-05-02)
   ------------------------------------------------------------
     #include <arpa/inet.h>
     uint16_t ntohs(uint16_t hostlong);
   Convert an unsigned 16-bit value from network to host byte order.
   Source: /usr/share/man/man3/ntohs.3.gz (local manual, paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
           musl-1.2.6-r6, ELF32 i386
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: ntohs, ELF VA 0x59efe; Ghidra image base 0x10000,
           global entry 0x69efe, RET 0x69f06.
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
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits ntohs_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition ntohs_spec (c : N) : N := revbytes c 2.
Theorem ntohs_spec_involutive : forall c,
  ntohs_spec (ntohs_spec c) = c.
Proof. intros. apply revbytes_involutive. Qed.

Definition ntohs_invs (s0 : store) :=
  leaf_invs 0x69efe 0x69f06 s0 (ntohs_spec (cdecl_arg s0)).
Definition ntohs_exit := at_address 0x69f06.

Theorem ntohs_nwc : forall s1 s2, ntohs_i386 s1 = ntohs_i386 s2.
Proof. reflexivity. Qed.

Theorem ntohs_preserves_memory :
  forall_endstates ntohs_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ntohs_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x69efe, s0)),
  satisfies_all ntohs_i386 (ntohs_invs s0) ntohs_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold ntohs_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold ntohs_invs, leaf_invs, ntohs_exit, at_address.
    all: repeat x86_step.
    all: try exact PRE.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, ntohs_spec, cdecl_arg.
    all: psimpl.
    all: repeat split; try reflexivity.
    all: apply bswap_load16.
Qed.

Theorem ntohs_correct :
  forall prog (EXT : ntohs_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x69efe, s0)),
  satisfies_all prog (ntohs_invs s0) ntohs_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := ntohs_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply ntohs_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem ntohs_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates ntohs_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem ntohs_returns :
  forall prog (EXT : ntohs_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x69f06,s) = (Addr 0x69efe,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x69f06,s)::t))
    (UT : unterminated ntohs_exit t),
  cdecl_returned s0 (ntohs_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x69efe) (ret := 0x69f06).
  - discriminate.
  - apply EXT. reflexivity.
  - apply ntohs_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
