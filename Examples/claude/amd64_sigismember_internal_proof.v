(* sigismember_internal -- test membership of a signal (unchecked)

   SEMANTICS
   ---------
   __sigismember(set, sig) is glibc's exported unchecked membership test, the
   core of sigismember(3) without the signal-number validation.  Signal sig is
   bit (sig-1) mod 64 of the 64-bit word (sig-1)/64 of the sigset_t.  The result
   is 1 if that bit is set and 0 otherwise.  For 1 <= sig <= 64 this is bit
   sig-1 of the first word, which is the same representation used in
   amd64_sigisemptyset_proof.v and amd64_sigemptyset_proof.v.

   SPECIFICATION (man 3 sigsetops, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <signal.h>
            int sigismember(const sigset_t *set, int signum);

     DESCRIPTION
            sigismember() tests whether signum is a member of set.

     RETURN VALUE
            sigismember()  returns  1  if signum is a member of set, 0 if signum is
            not a member, and -1 on error.

     (__sigismember performs no validation and has no error return.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol __sigismember at 0x275cb0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigismember_internal_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set; ESI = sig (int), with 1 <= sig <= 1024 (the 16 words of a
            sigset_t); m = memory.
   Output:  On return, RAX = 1 if bit (sig-1) mod 64 of the 8-byte word at
            set + 8*((sig-1)/64) is set, and RAX = 0 otherwise.  For
            1 <= sig <= 64 this is exactly sig_member m set sig
            (sigismember_first_word).
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import sigismember_internal_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigismember_internal_nwc: forall s2 s1, sigismember_internal_amd64 s1 = sigismember_internal_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigismember_internal_welltyped: welltyped_prog x64typctx sigismember_internal_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigismember_internal_preserves_memory:
  forall_endstates sigismember_internal_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem sigismember_internal_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigismember_internal_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 39.  Cut points: 18 (after the shift) and 23 (after
   the CMOVNS that picks the word index). *)
Definition sigismember_internal_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 39 => true
  | _ => false
  end | _ => false end.

Definition sig_word (m:memory) (set sig:N) := m Ⓠ[set ⊕ 8 * ((sig - 1) / 64)].

Definition postcondition (m set sig rsp:N) (s:store) :=
  s R_RAX = N.b2n (N.testbit (sig_word m set sig) ((sig - 1) mod 64)) /\ s R_RSP = rsp.

Definition sigismember_internal_invs (m set sig rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_RSI mod 2^32 = sig /\ s R_RSP = rsp)
  | 39 => Some (postcondition m set sig rsp s)
  | _ => None
  end | _ => None end.

Theorem sigismember_internal_correct:
  forall s t s' x' m set sig rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (SIG: s R_RSI mod 2^32 = sig)
         (RANGE: 1 <= sig <= 1024) (RSP: s R_RSP = rsp),
  satisfies_all sigismember_internal_amd64 (sigismember_internal_invs m set sig rsp)
                sigismember_internal_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigismember_internal_welltyped. intro MDL1.
  clear - PRE MDL1 RANGE. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [SET [SIG RSP]]].
  assert (F1: msub 32 (s1 R_RSI) 1 = sig - 1).
    unfold msub. change (2^32) with 4294967296 in *. lia.
  assert (F2: msub 6 (s1 R_RSI) 1 = (sig - 1) mod 64).
    unfold msub. change (2^32) with 4294967296 in *. change (2^6) with 64. lia.
  assert (F3: (sig - 1) >> 6 < 2^31).
    rewrite N.shiftr_div_pow2. change (2^6) with 64. change (2^31) with 2147483648.
    apply N.div_lt_upper_bound; lia.
  repeat x64_step.
  all: rewrite F1, ?N.shiftr_0_r, (N.mod_small (sig-1) (2^32)) in BC by (change (2^32) with 4294967296; lia).
  all: rewrite N.land_diag, slt32_0 in BC by (change (2^32) with 4294967296; lia).
  - (* sig - 1 < 0: impossible *)
    exfalso. rewrite testbit31_ge in BC by (change (2^32) with 4294967296; lia).
    apply N.leb_le in BC. change (2^31) with 2147483648 in BC. lia.
  - rewrite F1, F2, ?N.shiftr_0_r, (N.mod_small (sig-1) (2^32)) by (change (2^32) with 4294967296; lia).
    change (6 .& 31) with 6.
    rewrite ashiftr_nonneg, (N.mod_small (sig-1) (2^32)) by
      (rewrite ?N.mod_small; change (2^N.pred 32) with 2147483648; change (2^32) with 4294967296; lia).
    rewrite (N.mod_small ((sig-1) >> 6) (2^32)) by (change (2^32) with 4294967296; change (2^31) with 2147483648 in F3; lia).
    rewrite (N.mod_small ((sig-1) >> 6) (2^32)) by (change (2^32) with 4294967296; change (2^31) with 2147483648 in F3; lia).
    rewrite scast_32_64_small by exact F3.
    rewrite N.shiftl_1_l, <- getmem_mod_l, pow2_land_eqb0.
    split; [|assumption]. unfold sig_word.
    rewrite N.shiftr_div_pow2, (N.mul_comm _ 8). change (2^6) with 64.
    match goal with |- context [negb (N.testbit ?w ?k)] => destruct (N.testbit w k) end; reflexivity.
Qed.

(* For the 64 Linux signals, membership is bit sig-1 of the first word: the
   same representation used for sigemptyset and sigisemptyset. *)
Definition sig_member (m:memory) (set n:N) := N.testbit (m Ⓠ[set]) (n - 1).

Theorem sigismember_first_word:
  forall m set sig, 1 <= sig <= 64 ->
  N.b2n (N.testbit (sig_word m set sig) ((sig - 1) mod 64)) = N.b2n (sig_member m set sig).
Proof.
  intros m set sig R. unfold sig_word, sig_member.
  rewrite (N.div_small (sig - 1) 64), (N.mod_small (sig - 1) 64) by lia.
  rewrite N.mul_0_r, N.add_0_r, getmem_mod_l. reflexivity.
Qed.
