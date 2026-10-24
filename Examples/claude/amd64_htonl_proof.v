(* htonl -- convert a 32-bit value from host to network byte order

   SEMANTICS
   ---------
   htonl reverses the four bytes of its 32-bit argument.  amd64 is little-endian
   and network byte order is big-endian, so this converts host order to network
   order.  glibc's ntohl is the same function: both symbols resolve to the same
   code, so this proof covers ntohl too.

   SPECIFICATION (man 3 htonl, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <arpa/inet.h>
            uint32_t htonl(uint32_t hostlong);
            uint32_t ntohl(uint32_t netlong);

     DESCRIPTION
            The htonl() function converts the unsigned integer hostlong  from  host
            byte order to network byte order.

            The ntohl() function converts the unsigned integer netlong from network
            byte order to host byte order.

            On the i386 the host  byte  order  is  Least  Significant  Byte  first,
            whereas  the  network byte order, as used on the Internet, is Most Sig-
            nificant Byte first.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol htonl at 0x236610 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see htonl_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI (low 32 bits of RDI) holds hostlong = b3 b2 b1 b0 (b0 least significant).
   Output:  On return, RAX = b0 b1 b2 b3, i.e. RAX = bswap32(hostlong) with the
            upper 32 bits zero.  As a corollary (htonl_network_order), writing
            RAX to memory in the host's little-endian order produces the
            big-endian (network-order) encoding of hostlong.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import htonl_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem htonl_nwc: forall s2 s1, htonl_amd64 s1 = htonl_amd64 s2.
Proof. reflexivity. Qed.

Theorem htonl_welltyped: welltyped_prog x64typctx htonl_amd64.
Proof. Picinae_typecheck. Qed.

Theorem htonl_preserves_memory:
  forall_endstates htonl_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem htonl_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates htonl_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 8. *)
Definition htonl_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 8 => true
  | _ => false
  end | _ => false end.

(* byte i of x *)
Definition byte (x i:N) := xbits x (8*i) (8*i+8).

Definition bswap32 (x:N) :=
  (byte x 0 << 24) .| (byte x 1 << 16) .| (byte x 2 << 8) .| byte x 3.

Definition postcondition (h rsp:N) (s:store) :=
  s R_RAX = bswap32 h /\ s R_RSP = rsp.

Definition htonl_invs (h rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI mod 2^32 = h /\ s R_RSP = rsp)
  | 8 => Some (postcondition h rsp s)
  | _ => None
  end | _ => None end.

Theorem htonl_correct:
  forall s t s' x' h rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (H: s R_RDI mod 2^32 = h) (RSP: s R_RSP = rsp),
  satisfies_all htonl_amd64 (htonl_invs h rsp) htonl_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply htonl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [H RSP].
  repeat x64_step.
  split; [|assumption].
  rewrite <- H. unfold bswap32, byte. simpl (8*_). simpl (_+8).
  bitblast_upto 32.
Qed.

(* Storing the result in host (little-endian) order yields the network
   (big-endian) encoding of the argument. *)
Theorem htonl_network_order:
  forall m a h,
  getmem 64 BigE 4 (setmem 64 LittleE 4 m a (bswap32 h)) a = h mod 2^32.
Proof.
  intros.
  rewrite <- (revbytes_involutive (getmem _ BigE _ _ _) 4), revbytes_getmem,
          getmem_setmem by discriminate.
  unfold bswap32, byte. simpl (8*_). simpl (_+8). simpl (4*8).
  bitblast_upto 32.
Qed.
