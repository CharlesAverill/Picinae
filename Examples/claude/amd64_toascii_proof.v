(* toascii -- convert character to ASCII

   SEMANTICS
   ---------
   toascii clears every bit of its int argument except the low 7, producing
   a value in [0, 127].

   SPECIFICATION (man 3 toascii, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int toascii(int c);

     DESCRIPTION
            toascii()  converts c to a 7-bit unsigned char value that fits into the
            ASCII character set, by clearing the high-order bits.

     RETURN VALUE
            The value returned is that of the converted character.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see toascii_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI (low 32 bits of RDI) holds c.
   Output:  On return, RAX = c & 0x7f; in particular EAX (the int result) is the
            low 7 bits of c and lies in [0, 127].
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import toascii_amd64.
Import X64Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem toascii_nwc: forall s2 s1, toascii_amd64 s1 = toascii_amd64 s2.
Proof. reflexivity. Qed.

Theorem toascii_welltyped: welltyped_prog x64typctx toascii_amd64.
Proof. Picinae_typecheck. Qed.

Theorem toascii_preserves_memory:
  forall_endstates toascii_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem toascii_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates toascii_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 9. *)
Definition toascii_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 9 => true
  | _ => false
  end | _ => false end.

Definition postcondition (c rsp:N) (s:store) :=
  s R_RAX = c .& 127 /\ s R_RSP = rsp.

Definition toascii_invs (c rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI mod 2^32 = c /\ s R_RSP = rsp)
  | 9 => Some (postcondition c rsp s)
  | _ => None
  end | _ => None end.

Theorem toascii_correct:
  forall s t s' x' c rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (C: s R_RDI mod 2^32 = c) (RSP: s R_RSP = rsp),
  satisfies_all toascii_amd64 (toascii_invs c rsp) toascii_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply toascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [C RSP].
  repeat x64_step.
  split; [|assumption].
  rewrite <- C, N_mod_mod_pow by discriminate. reflexivity.
Qed.
