(* sigisemptyset -- test whether a signal set is empty

   SEMANTICS
   ---------
   sigisemptyset reports whether a signal set contains no signals.  glibc
   represents signal n (1 <= n <= 64) as bit n-1 of the first 64-bit word of
   sigset_t; sigismember, sigaddset and sigdelset use this representation.

   THIS IMPLEMENTATION DOES NOT MEET ITS SPECIFICATION.  glibc 2.35 computes
   the result through an int, truncating the first 64-bit word to its low 32
   bits.  The machine code tests only the 4 bytes at set[0..4), so a set whose
   members are all signals 33..64 is reported as empty.  Those signals include
   SIGRTMIN = 34 and every other real-time signal.  The theorem
   sigisemptyset_ignores_rt_signals below proves this for the binary, and the
   behavior was also observed by running the system libc (a test program that
   adds SIGRTMIN to an empty set gets sigisemptyset = 1).

   SPECIFICATION (man 3 sigsetops, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <signal.h>
            int sigisemptyset(const sigset_t *set);

     DESCRIPTION
        Glibc extensions
            If  the  _GNU_SOURCE feature test macro is defined, then <signal.h> ex-
            poses three other functions for manipulating signal sets:

            int sigisemptyset(const sigset_t *set);
            [...]
            sigisemptyset() returns 1 if set contains no signals, and 0 otherwise.

     (sigsetops(3) also says these functions set errno on error; glibc's
      sigisemptyset returns -1 with errno = EINVAL when set is NULL.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigisemptyset at 0x143070 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigisemptyset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set; m = memory on entry; fs = FS_BASE (thread pointer).
   Output:  If set <> NULL: RAX = 1 if the 32-bit word m[set] is 0, else RAX = 0,
              and memory is unchanged.
            If set = NULL: RAX = 0xffffffff (int -1), and the only memory change
              is errno = EINVAL (22): the 4-byte store at fs + m[GOT], where
              GOT = 0x319e10 is the GOT slot holding errno's TLS offset.
   Model:   The GOT slot is a rip-relative reference, so Ghidra resolved it to an
            absolute address for libc loaded at its image base 0x100000.
   Spec:    sigisemptyset_ignores_rt_signals: for every set containing only
            signals 33..64 (e.g. {SIGRTMIN}), the result is 1, which contradicts
            the man page.  sigisemptyset_sound_low: for sets containing only
            signals 1..32, the result is correct.
   Frame:   RSP is unchanged at both RETs, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import sigisemptyset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigisemptyset_nwc: forall s2 s1, sigisemptyset_amd64 s1 = sigisemptyset_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigisemptyset_welltyped: welltyped_prog x64typctx sigisemptyset_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigisemptyset_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigisemptyset_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 18 and 43. *)
Definition sigisemptyset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 18 | 43 => true
  | _ => false
  end | _ => false end.

(* glibc's membership: signal n (1..64) is bit n-1 of the first word. *)
Definition sig_member (m:memory) (set n:N) := N.testbit (m Ⓠ[set]) (n - 1).
Definition sig_empty (m:memory) (set:N) := forall n, 1 <= n <= 64 -> sig_member m set n = false.

Definition errno_slot := 0x319e10.

Definition postcondition (m set fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  if set =? 0 then s R_RAX = 0xffffffff /\ s V_MEM64 = m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22]
  else s R_RAX = (if m Ⓓ[set] =? 0 then 1 else 0) /\ s V_MEM64 = m.

Definition sigisemptyset_invs (m set fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 18 | 43 => Some (postcondition m set fs rsp s)
  | _ => None
  end | _ => None end.

Theorem sigisemptyset_correct:
  forall s t s' x' m set fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (FS: s R_FS_BASE = fs)
         (RSP: s R_RSP = rsp),
  satisfies_all sigisemptyset_amd64 (sigisemptyset_invs m set fs rsp)
                sigisemptyset_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigisemptyset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [SET [FS RSP]]].
  repeat x64_step.
  all: split; [assumption|]; rewrite BC; split;
       try reflexivity; unfold errno_slot; rewrite setmem_mod_l; reflexivity.
Qed.

(* The 4-byte test sees exactly signals 1..32. *)
Lemma low_word: forall (m:memory) set, m Ⓓ[set] = m Ⓠ[set] mod 2^32.
Proof. intros. rewrite (getmem_mod 64 LittleE 4 8). reflexivity. Qed.

(* THE BUG: a non-empty set of real-time signals is reported as empty. *)
Theorem sigisemptyset_ignores_rt_signals:
  forall m set,
  (forall n, 1 <= n <= 32 -> sig_member m set n = false) ->
  (if m Ⓓ[set] =? 0 then 1 else 0) = 1.
Proof.
  intros m set LOW. rewrite low_word.
  replace (m Ⓠ[set] mod 2^32) with 0. reflexivity.
  symmetry. apply N.bits_inj_0. intro i. rewrite Nmod_pow2_bits.
  destruct (N.ltb_spec i 32). 2: reflexivity.
  simpl. specialize (LOW (i+1)). unfold sig_member in LOW. rewrite N.add_sub in LOW. apply LOW. lia.
Qed.

(* A concrete witness: the set {SIGRTMIN} (SIGRTMIN = 34 on Linux/glibc). *)
Corollary sigisemptyset_rtmin_counterexample:
  forall m set, m Ⓠ[set] = 2^33 ->
  ~ sig_empty m set /\ (if m Ⓓ[set] =? 0 then 1 else 0) = 1.
Proof.
  intros m set W. split.
    intro E. specialize (E 34). unfold sig_member in E. rewrite W in E. discriminate E. lia.
    apply sigisemptyset_ignores_rt_signals. intros n N. unfold sig_member. rewrite W.
    rewrite N.pow2_bits_eqb. apply N.eqb_neq. lia.
Qed.

(* For sets of signals 1..32, the result is correct. *)
Theorem sigisemptyset_sound_low:
  forall m set,
  (forall n, 33 <= n <= 64 -> sig_member m set n = false) ->
  ((if m Ⓓ[set] =? 0 then 1 else 0) = 1 <-> sig_empty m set).
Proof.
  intros m set HIGH. rewrite low_word. split.
  - intros R n N. unfold sig_member.
    destruct (N.eqb_spec (m Ⓠ[set] mod 2^32) 0) as [Z|Z]; [|discriminate R].
    destruct (N.lt_ge_cases n 33).
      rewrite <- (N.mod_small (n-1) 32) at 1 by lia.
      replace (N.testbit (m Ⓠ[set]) ((n-1) mod 32)) with (N.testbit (m Ⓠ[set] mod 2^32) (n-1)).
        rewrite Z. apply N.bits_0.
        rewrite Nmod_pow2_bits, N.mod_small by lia. replace (n-1 <? 32) with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
      apply HIGH. lia.
  - intro E. replace (m Ⓠ[set] mod 2^32) with 0. reflexivity.
    symmetry. apply N.bits_inj_0. intro i. rewrite Nmod_pow2_bits.
    destruct (N.ltb_spec i 32). 2: reflexivity.
    simpl. specialize (E (i+1)). unfold sig_member in E. rewrite N.add_sub in E. apply E. lia.
Qed.
