(* pthread_equal -- compare thread IDs

   SEMANTICS
   ---------
   pthread_equal compares two thread identifiers.  In glibc, pthread_t is an
   unsigned long, so the comparison is 64-bit integer equality.  It returns
   exactly 1 when they are equal and 0 otherwise.

   SPECIFICATION (man 3 pthread_equal, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <pthread.h>
            int pthread_equal(pthread_t t1, pthread_t t2);

     DESCRIPTION
            The pthread_equal() function compares two thread identifiers.

     RETURN VALUE
            If  the  two  thread  IDs  are equal, pthread_equal() returns a nonzero
            value; otherwise, it returns 0.

     ERRORS
            This function always succeeds.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol pthread_equal at 0x195c70 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see pthread_equal_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = t1, RSI = t2 (pthread_t = unsigned long, 64 bits).
   Output:  On return, RAX = 1 if t1 = t2, and RAX = 0 otherwise.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import pthread_equal_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem pthread_equal_nwc: forall s2 s1, pthread_equal_amd64 s1 = pthread_equal_amd64 s2.
Proof. reflexivity. Qed.

Theorem pthread_equal_welltyped: welltyped_prog x64typctx pthread_equal_amd64.
Proof. Picinae_typecheck. Qed.

Theorem pthread_equal_preserves_memory:
  forall_endstates pthread_equal_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem pthread_equal_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates pthread_equal_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 12. *)
Definition pthread_equal_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 12 => true
  | _ => false
  end | _ => false end.

Definition postcondition (tid1 tid2 rsp:N) (s:store) :=
  s R_RAX = (if tid1 =? tid2 then 1 else 0) /\ s R_RSP = rsp.

Definition pthread_equal_invs (tid1 tid2 rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI = tid1 /\ s R_RSI = tid2 /\ s R_RSP = rsp)
  | 12 => Some (postcondition tid1 tid2 rsp s)
  | _ => None
  end | _ => None end.

Theorem pthread_equal_correct:
  forall s t s' x' tid1 tid2 rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (T1: s R_RDI = tid1) (T2: s R_RSI = tid2) (RSP: s R_RSP = rsp),
  satisfies_all pthread_equal_amd64 (pthread_equal_invs tid1 tid2 rsp) pthread_equal_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply pthread_equal_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [T1 [T2 RSP]].
  repeat x64_step.
  split; [reflexivity|assumption].
Qed.
