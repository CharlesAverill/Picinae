(* mbsinit -- test for initial shift state

   SEMANTICS
   ---------
   mbsinit reports whether a conversion state is the initial state.  In glibc,
   mbstate_t is struct { int __count; union { ... } __value; }, and a state is
   initial exactly when __count == 0.  A NULL pointer also counts as initial.
   glibc returns exactly 1 or 0.

   SPECIFICATION (man 3 mbsinit, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            int mbsinit(const mbstate_t *ps);

     DESCRIPTION
            [...]
            One  possible  way to create an mbstate_t in initial state is to set it
            to zero:

                mbstate_t state;
                memset(&state, 0, sizeof(state));

            [...]
            The  function  mbsinit()  tests  whether  *ps corresponds to an initial
            state.

     RETURN VALUE
            mbsinit() returns nonzero if *ps is an initial state, or if ps is NULL.
            Otherwise, it returns 0.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol mbsinit at 0x1c5f60 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see mbsinit_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = ps; m = memory on entry.
   Output:  On return, RAX = 1 if ps = NULL or the 4-byte __count field m[ps] is 0,
            and RAX = 0 otherwise.  Corollary (mbsinit_zeroed): a state whose
            first 4 bytes are zero, e.g. one cleared with memset as the man page
            suggests, is reported as initial.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import mbsinit_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem mbsinit_nwc: forall s2 s1, mbsinit_amd64 s1 = mbsinit_amd64 s2.
Proof. reflexivity. Qed.

Theorem mbsinit_welltyped: welltyped_prog x64typctx mbsinit_amd64.
Proof. Picinae_typecheck. Qed.

Theorem mbsinit_preserves_memory:
  forall_endstates mbsinit_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem mbsinit_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates mbsinit_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 23. *)
Definition mbsinit_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 23 => true
  | _ => false
  end | _ => false end.

Definition mbsinit_result (m:memory) (ps:N) :=
  if ps =? 0 then 1 else if m Ⓓ[ps] =? 0 then 1 else 0.

Definition postcondition (m ps rsp:N) (s:store) :=
  s R_RAX = mbsinit_result m ps /\ s R_RSP = rsp.

Definition mbsinit_invs (m ps rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = ps /\ s R_RSP = rsp)
  | 23 => Some (postcondition m ps rsp s)
  | _ => None
  end | _ => None end.

Theorem mbsinit_correct:
  forall s t s' x' m ps rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (PS: s R_RDI = ps) (RSP: s R_RSP = rsp),
  satisfies_all mbsinit_amd64 (mbsinit_invs m ps rsp) mbsinit_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply mbsinit_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [PS RSP]].
  repeat x64_step.
  all: split; [|assumption]; unfold mbsinit_result; rewrite BC; reflexivity.
Qed.

Theorem mbsinit_zeroed:
  forall m ps, ps <> 0 -> m Ⓓ[ps] = 0 -> mbsinit_result m ps = 1.
Proof.
  intros m ps NZ Z. unfold mbsinit_result.
  rewrite (proj2 (N.eqb_neq _ _) NZ), Z. reflexivity.
Qed.
