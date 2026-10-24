(* sigemptyset -- initialize an empty signal set

   SEMANTICS
   ---------
   sigemptyset initializes a signal set to contain no signals.  glibc
   represents signal n (1 <= n <= 64) as bit n-1 of the first 64-bit word of
   sigset_t (the same representation as sigismember/sigaddset).  sigemptyset
   therefore clears only those 8 bytes, even though sigset_t is 128 bytes; the
   remaining 120 bytes are left untouched.  A NULL set fails with
   errno = EINVAL.

   SPECIFICATION (man 3 sigsetops, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <signal.h>
            int sigemptyset(sigset_t *set);

     DESCRIPTION
            These functions allow the manipulation of POSIX signal sets.

            sigemptyset() initializes the signal set given by set  to  empty,  with
            all signals excluded from the set.

     RETURN VALUE
            sigemptyset(), sigfillset(), sigaddset(), and sigdelset() return  0  on
            success and -1 on error.

            On error, these functions set errno to indicate the cause of the error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigemptyset at 0x142e40 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigemptyset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set; m = memory on entry; fs = FS_BASE (thread pointer).
   Output:  If set <> NULL: RAX = 0 and memory = m[set := 0] (8-byte store).  So
              every signal 1..64 is excluded (sigemptyset_empty), and no byte
              outside set[0..8) changes.
            If set = NULL: RAX = 0xffffffff (int -1), and the only memory change
              is errno = EINVAL (22), stored at fs + m[0x319e10] (the GOT slot
              holding errno's TLS offset).
   Model:   The GOT slot is a rip-relative reference, so Ghidra resolved it to an
            absolute address for libc loaded at its image base 0x100000.
   Frame:   RSP is unchanged at both RETs, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import sigemptyset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigemptyset_nwc: forall s2 s1, sigemptyset_amd64 s1 = sigemptyset_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigemptyset_welltyped: welltyped_prog x64typctx sigemptyset_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigemptyset_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigemptyset_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 18 and 38. *)
Definition sigemptyset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 18 | 38 => true
  | _ => false
  end | _ => false end.

Definition sig_member (m:memory) (set n:N) := N.testbit (m Ⓠ[set]) (n - 1).

Definition errno_slot := 0x319e10.

Definition postcondition (m set fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  if set =? 0 then s R_RAX = 0xffffffff /\ s V_MEM64 = m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22]
  else s R_RAX = 0 /\ s V_MEM64 = m [Ⓠ set := 0].

Definition sigemptyset_invs (m set fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 18 | 38 => Some (postcondition m set fs rsp s)
  | _ => None
  end | _ => None end.

Theorem sigemptyset_correct:
  forall s t s' x' m set fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (FS: s R_FS_BASE = fs)
         (RSP: s R_RSP = rsp),
  satisfies_all sigemptyset_amd64 (sigemptyset_invs m set fs rsp)
                sigemptyset_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigemptyset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [SET [FS RSP]]].
  repeat x64_step.
  all: split; [assumption|]; rewrite BC; split;
       try reflexivity; unfold errno_slot; rewrite setmem_mod_l; reflexivity.
Qed.

(* The man page's guarantee: afterwards no signal is a member. *)
Theorem sigemptyset_empty:
  forall (m:memory) set n, sig_member (m [Ⓠ set := 0]) set n = false.
Proof.
  intros. unfold sig_member. rewrite getmem_setmem by discriminate. apply N.bits_0.
Qed.
