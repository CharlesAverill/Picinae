(* htonl (AArch64 / ARMv8) -- convert a 32-bit value from host to network order.

   SEMANTICS
   ---------
   htonl reverses the four bytes of its 32-bit argument (little-endian host order
   to big-endian network order).  glibc's ntohl resolves to the same code, so this
   proof covers ntohl too.  On AArch64 the compiler emits a single `rev w0,w0`,
   realized here as a 32-bit rev16 (`(w0 & 0xff00ff00) >> 8 | (w0 & 0x00ff00ff) <<
   8`) followed by a halfword rotate (`>> 16 | << 16`), whose net effect is the
   full 4-byte reversal.

   SPECIFICATION (man 3 htonl, Linux man-pages)
   --------------------------------------------
     uint32_t htonl(uint32_t hostlong);
     The htonl() function converts the unsigned integer hostlong from host byte
     order to network byte order.  On the i386 the host byte order is Least
     Significant Byte first, whereas the network byte order is Most Significant
     Byte first.

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
            symbol htonl at 0x1f9cf0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Model:   Specification and proof written by Claude Opus 4.8 (claude-opus-4-8),
            an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   W0 (low 32 bits of X0) holds hostlong.
   Output:  X0 = bswap32 of the low 32 input bits, zero-extended to 64.  Memory
            and the stack pointer are unchanged (leaf function, returns via X30).
 *)

Require Import Picinae_armv8.
Require Import htonl_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem htonl_nwc: forall s2 s1, htonl_arm8 s1 = htonl_arm8 s2.
Proof. reflexivity. Qed.
Theorem htonl_welltyped: welltyped_prog arm8typctx htonl_arm8.
Proof. Picinae_typecheck. Qed.
Theorem htonl_preserves_memory:
  forall_endstates htonl_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* The RET is at offset 4. *)
Definition htonl_exit (t:trace) :=
  match t with (Addr 4,_)::_ => true | _ => false end.

Definition byte (x i:N) := xbits x (8*i) (8*i+8).
Definition bswap32 (x:N) :=
  (byte x 0 << 24) .| (byte x 1 << 16) .| (byte x 2 << 8) .| byte x 3.

Definition postcondition (x0:N) (s:store) := s R_X0 = bswap32 x0.

Definition htonl_invs (x0:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 = x0)
  | 4 => Some (postcondition x0 s)
  | _ => None
  end | _ => None end.

Theorem htonl_correct:
  forall s t s' x' x0
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (X0: s R_X0 = x0),
  satisfies_all htonl_arm8 (htonl_invs x0) htonl_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply htonl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into X0.
  repeat arm8_step.
  unfold postcondition, bswap32, byte. simpl (8*_). simpl (_+8).
  bitblast_upto 32.
Qed.
