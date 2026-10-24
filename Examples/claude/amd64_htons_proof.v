(* htons -- convert a 16-bit value from host to network byte order

   SEMANTICS
   ---------
   htons swaps the two bytes of its 16-bit argument, which converts little-endian
   host order to big-endian network order.  glibc's ntohs is the same function:
   both symbols resolve to the same code, so this proof covers ntohs too.

   SPECIFICATION (man 3 htons, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <arpa/inet.h>
            uint16_t htons(uint16_t hostshort);
            uint16_t ntohs(uint16_t netshort);

     DESCRIPTION
            The htons() function converts the unsigned short integer hostshort from
            host byte order to network byte order.

            The  ntohs() function converts the unsigned short integer netshort from
            network byte order to host byte order.

            On the i386 the host  byte  order  is  Least  Significant  Byte  first,
            whereas  the  network byte order, as used on the Internet, is Most Sig-
            nificant Byte first.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol htons at 0x236620 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see htons_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   DI (low 16 bits of RDI) holds hostshort = b1 b0 (b0 least significant).
            The ABI leaves bits 16-63 of RDI unspecified for a uint16_t argument.
   Output:  On return, AX (the uint16_t result, low 16 bits of RAX) = b0 b1.
            The exact full-register effect is also proved: bits 16-31 of RAX are
            copied from EDI, and bits 32-63 are zero.  Callers must not rely on
            any of this, since the ABI leaves bits 16-63 of the result unspecified.
            As a corollary (htons_network_order), writing AX to memory in host
            (little-endian) order produces the big-endian encoding of hostshort.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import htons_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem htons_nwc: forall s2 s1, htons_amd64 s1 = htons_amd64 s2.
Proof. reflexivity. Qed.

Theorem htons_welltyped: welltyped_prog x64typctx htons_amd64.
Proof. Picinae_typecheck. Qed.

Theorem htons_preserves_memory:
  forall_endstates htons_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem htons_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates htons_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 10. *)
Definition htons_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 10 => true
  | _ => false
  end | _ => false end.

Definition byte (x i:N) := xbits x (8*i) (8*i+8).

Definition bswap16 (x:N) := (byte x 0 << 8) .| byte x 1.

Definition postcondition (rdi rsp:N) (s:store) :=
  s R_RAX mod 2^16 = bswap16 rdi /\
  s R_RAX = (rdi mod 2^32) .& 0xffff0000 .| bswap16 rdi /\
  s R_RSP = rsp.

Definition htons_invs (rdi rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI = rdi /\ s R_RSP = rsp)
  | 10 => Some (postcondition rdi rsp s)
  | _ => None
  end | _ => None end.

Theorem htons_correct:
  forall s t s' x' rdi rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (RDI: s R_RDI = rdi) (RSP: s R_RSP = rsp),
  satisfies_all htons_amd64 (htons_invs rdi rsp) htons_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply htons_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [RDI RSP].
  repeat x64_step.
  unfold bswap16, byte. simpl (8*_). simpl (_+8).
  split; [|split; [|assumption]].
    bitblast_upto 16.
    bitblast_upto 32.
Qed.

Theorem htons_network_order:
  forall m a h,
  getmem 64 BigE 2 (setmem 64 LittleE 2 m a (bswap16 h)) a = h mod 2^16.
Proof.
  intros.
  rewrite <- (revbytes_involutive (getmem _ BigE _ _ _) 2), revbytes_getmem,
          getmem_setmem by discriminate.
  unfold bswap16, byte. simpl (8*_). simpl (_+8). simpl (2*8).
  bitblast_upto 16.
Qed.
