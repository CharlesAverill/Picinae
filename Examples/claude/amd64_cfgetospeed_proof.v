(* cfgetospeed -- get the output baud rate of a termios structure

   SEMANTICS
   ---------
   cfgetospeed returns the output baud rate stored in a termios structure.  In
   glibc on Linux, the rate lives in the CBAUD | CBAUDEX bits (mask 0x100f) of
   the c_cflag field, which is the third 32-bit field (offset 8).

   SPECIFICATION (man 3 termios, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <termios.h>
            #include <unistd.h>
            speed_t cfgetispeed(const struct termios *termios_p);
            speed_t cfgetospeed(const struct termios *termios_p);

     DESCRIPTION
        Line control
            [...]
            The baud rate functions are provided for getting and setting the values
            of the input and output baud rates in the termios structure.  The new
            values do not take effect until tcsetattr() is successfully called.
            [...]
            cfgetospeed() returns the output baud rate stored in the termios struc-
            ture pointed to by termios_p.
            [...]
            cfgetispeed() returns the input baud rate stored in the termios struc-
            ture.

     RETURN VALUE
            cfgetispeed() returns the input baud rate stored in the termios struc-
            ture.

            cfgetospeed() returns the output baud rate stored in the termios struc-
            ture.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol cfgetospeed at 0x219c30 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see cfgetospeed_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = termios_p; m = memory on entry.
   Output:  On return, RAX = m[termios_p+8] & 0x100f (c_cflag & (CBAUD|CBAUDEX), a
            speed_t constant such as B9600).
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import cfgetospeed_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem cfgetospeed_nwc: forall s2 s1, cfgetospeed_amd64 s1 = cfgetospeed_amd64 s2.
Proof. reflexivity. Qed.

Theorem cfgetospeed_welltyped: welltyped_prog x64typctx cfgetospeed_amd64.
Proof. Picinae_typecheck. Qed.

Theorem cfgetospeed_preserves_memory:
  forall_endstates cfgetospeed_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem cfgetospeed_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates cfgetospeed_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition cfspeed (m:memory) (p:N) := m Ⓓ[p ⊕ 8] .& 0x100f.

(* The RET is at offset 12. *)
Definition cfgetospeed_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 12 => true
  | _ => false
  end | _ => false end.

Definition postcondition (m p rsp:N) (s:store) :=
  s R_RAX = cfspeed m p /\ s R_RSP = rsp.

Definition cfgetospeed_invs (m p rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = rsp)
  | 12 => Some (postcondition m p rsp s)
  | _ => None
  end | _ => None end.

Theorem cfgetospeed_correct:
  forall s t s' x' m p rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (RSP: s R_RSP = rsp),
  satisfies_all cfgetospeed_amd64 (cfgetospeed_invs m p rsp) cfgetospeed_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfgetospeed_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [P RSP]].
  repeat x64_step.
  all: split; [|assumption]; unfold cfspeed; rewrite getmem_dw_w, land_mod_pow2, getmem_mod_l, N.add_comm by reflexivity; reflexivity.
Qed.
