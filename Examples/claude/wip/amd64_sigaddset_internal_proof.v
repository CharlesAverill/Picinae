(* sigaddset_internal -- add a signal to a signal set (unchecked)

   SEMANTICS
   ---------
   __sigaddset(set, sig) is glibc's exported unchecked core of sigaddset(3),
   without the signal-number validation.  It sets bit (sig-1) mod 64 of the
   64-bit word (sig-1)/64 of the sigset_t and returns 0.

   SPECIFICATION (man 3 sigsetops, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <signal.h>
            int sigaddset(sigset_t *set, int signum);

     DESCRIPTION
            sigaddset()  and  sigdelset() add and delete respectively signal signum
            from set.

     RETURN VALUE
            sigemptyset(), sigfillset(), sigaddset(), and sigdelset() return  0  on
            success and -1 on error.

     (__sigaddset performs no validation and always returns 0.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol __sigaddset at 0x275ce0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigaddset_internal_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set; ESI = sig (int), with 1 <= sig <= 1024 (the 16 words of a
            sigset_t); m = memory.
   Output:  On return, RAX = 0, and memory is m with the 8-byte word
            w = m[set + 8*((sig-1)/64)] replaced by w | 2^((sig-1) mod 64).
            Corollaries for 1 <= sig <= 64 (the Linux signals, first word):
            sigaddset_adds (sig is a member afterwards) and sigaddset_others (all
            other signals keep their membership).
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import sigaddset_internal_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigaddset_internal_nwc: forall s2 s1, sigaddset_internal_amd64 s1 = sigaddset_internal_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigaddset_internal_welltyped: welltyped_prog x64typctx sigaddset_internal_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigaddset_internal_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigaddset_internal_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 34; offset 17 is a cut point between SUB and CMOVNS. *)
Definition sigaddset_internal_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 34 => true
  | _ => false
  end | _ => false end.

Definition word_addr (set sig:N) := set ⊕ 8 * ((sig - 1) / 64).

Definition sigaddset_mem (m:memory) (set sig:N) :=
  m [Ⓠ word_addr set sig := m Ⓠ[word_addr set sig] .| 2^((sig - 1) mod 64)].

Definition postcondition (m set sig rsp:N) (s:store) :=
  s V_MEM64 = sigaddset_mem m set sig /\ s R_RAX = 0 /\ s R_RSP = rsp.

Definition sigaddset_internal_invs (m set sig rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_RSI mod 2^32 = sig /\ s R_RSP = rsp)
  | 17 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_RCX = sig - 1 /\ s R_RDX = 1 /\
                s R_SF = 0 /\ s R_RSP = rsp)
  | 34 => Some (postcondition m set sig rsp s)
  | _ => None
  end | _ => None end.

Theorem sigaddset_internal_correct:
  forall s t s' x' m set sig rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (SIG: s R_RSI mod 2^32 = sig)
         (RANGE: 1 <= sig <= 1024) (RSP: s R_RSP = rsp),
  satisfies_all sigaddset_internal_amd64 (sigaddset_internal_invs m set sig rsp)
                sigaddset_internal_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigaddset_internal_welltyped. intro MDL1.
  clear - PRE MDL1 RANGE. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [MEM [SET [SIG RSP]]].
    assert (SL: sig < 2^32) by (rewrite <- SIG; apply mp2_mod_lt).
    repeat x64_step.
    rewrite SIG. assert (S32: sig >> 32 = 0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact SL).
    rewrite S32, ?N.shiftr_0_r, N.Div0.mod_0_l, N.shiftl_0_l, N.lor_0_l, (N.mod_small sig (2^32)) by exact SL.
    Show.
    assert (M: msub 32 sig 1 = sig - 1) by (unfold msub; change (2^32) with 4294967296 in *; lia).
    rewrite M, !(N.mod_small (sig - 1) (2^32)) by (change (2^32) with 4294967296 in *; lia).
    rewrite slt32_0, testbit31_ge by (change (2^32) with 4294967296 in *; lia).
    replace (2^31 <=? sig - 1) with false by (symmetry; apply N.leb_gt; change (2^31) with 2147483648; lia).
    repeat split; try assumption; try reflexivity.
    unfold msub. change (2^32) with 4294967296 in *. lia.
  - destruct PRE as [MEM [SET [RCX [RDX [SF RSP]]]]].
    assert (F3: (sig - 1) >> 6 < 2^31).
      rewrite N.shiftr_div_pow2. change (2^6) with 64. change (2^31) with 2147483648.
      apply N.div_lt_upper_bound; lia.
    repeat x64_step.
    rewrite ?N.shiftr_0_r, !(N.mod_small (sig - 1) (2^32)) by (change (2^32) with 4294967296; lia).
    change (6 .& 31) with 6.
    rewrite ashiftr_nonneg, (N.mod_small (sig-1) (2^32)) by
      (rewrite ?N.mod_small; change (2^N.pred 32) with 2147483648; change (2^32) with 4294967296; lia).
    rewrite !(N.mod_small ((sig-1) >> 6) (2^32)) by (change (2^32) with 4294967296; change (2^31) with 2147483648 in F3; lia).
    rewrite scast_32_64_small by exact F3.
    rewrite N.shiftl_1_l, <- setmem_mod_l, <- getmem_mod_l.
    split; [|split; [reflexivity|assumption]].
    unfold sigaddset_mem, word_addr.
    rewrite N.shiftr_div_pow2, (N.mul_comm _ 8). change (2^6) with 64. reflexivity.
Qed.

(* For the 64 Linux signals (first word): sig is a member afterwards, and
   every other signal keeps its membership. *)
Lemma sigaddset_first_word:
  forall (m:memory) set sig, 1 <= sig <= 64 ->
  (sigaddset_mem m set sig) Ⓠ[set] = m Ⓠ[set] .| 2^(sig - 1).
Proof.
  intros m set sig R. unfold sigaddset_mem, word_addr.
  rewrite (N.div_small (sig - 1) 64), (N.mod_small (sig - 1) 64) by lia.
  rewrite N.mul_0_r, N.add_0_r, <- (getmem_mod_l _ _ _ _ set), getmem_setmem by discriminate.
  apply N.mod_small. apply lor_bound. apply getmem_bound.
  change (8*8) with 64. apply N.pow_lt_mono_r; lia.
Qed.

Theorem sigaddset_adds:
  forall (m:memory) set sig, 1 <= sig <= 64 ->
  N.testbit ((sigaddset_mem m set sig) Ⓠ[set]) (sig - 1) = true.
Proof.
  intros. rewrite sigaddset_first_word, N.lor_spec, N.pow2_bits_true by assumption.
  apply Bool.orb_true_r.
Qed.

Theorem sigaddset_others:
  forall (m:memory) set sig n, 1 <= sig <= 64 -> 1 <= n <= 64 -> n <> sig ->
  N.testbit ((sigaddset_mem m set sig) Ⓠ[set]) (n - 1) = N.testbit (m Ⓠ[set]) (n - 1).
Proof.
  intros. rewrite sigaddset_first_word, N.lor_spec, N.pow2_bits_eqb by assumption.
  replace (sig - 1 =? n - 1) with false by (symmetry; apply N.eqb_neq; lia).
  apply Bool.orb_false_r.
Qed.
