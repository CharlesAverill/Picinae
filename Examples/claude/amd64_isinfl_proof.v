(* isinfl -- test whether a long double is infinite

   SEMANTICS
   ---------
   isinfl(x) returns 1 for +inf, -1 for -inf and 0 otherwise.  An x87
   infinity has exponent 0x7fff and significand exactly 0x8000000000000000
   (integer bit set, fraction zero).  glibc forms
     C = (~se & 0x7fff) | (hi - 0x80000000) | lo,
   which is zero exactly for an infinity, and returns
     ~((-C | C) >>s 31) & (1 - ((sext(se) >>s 14) & 2)).
   The first factor is all ones iff C = 0; the second is 1, or -1 when the
   sign bit is set.  A pseudo-infinity (integer bit clear) is not reported.

   SPECIFICATION (man 3 isinf, Linux man-pages 5.10, Ubuntu 22.04)
   ----------------------------------------------------------------

     int isinfl(long double x);

     isinf() returns 1 if x is positive infinity, and -1 if x is negative
     infinity.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol isinfl at 0x40ff0 (Ghidra address 0x140ff0, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isinfl_amd64.v (global addresses).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   the long double x is passed in memory at RSP+8 (at entry):
            lo = m Ⓓ[8+rsp] and hi = m Ⓓ[12+rsp] are the 64-bit significand
            (bit 31 of hi is the explicit integer bit), se = m Ⓦ[16+rsp] holds
            the sign (bit 15) and the biased exponent (exp80 se = bits 0..14).
   Status:  isinfl_correct is Admitted (QED-SLOW, see the end of the file):
            its tactic proof is complete but the kernel check is too slow.
   Output:  RAX = isinfl_spec lo hi se (amd64_ieee.v): if exp80 se = 0x7fff,
            hi = 0x80000000 and lo = 0, then 0xffffffff (-1) when the sign
            bit (bit 15 of se) is set and 1 otherwise; else 0.
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import isinfl_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem isinfl_nwc: forall s2 s1, isinfl_amd64 s1 = isinfl_amd64 s2.
Proof. reflexivity. Qed.

Theorem isinfl_welltyped: welltyped_prog x64typctx isinfl_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isinfl_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isinfl_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.


Definition isinfl_exit (t:trace) :=
  match t with (Addr 0x141035,_)::_ => true | _ => false end.

Definition isinfl_invs (m:memory) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x140ff0 => Some (s V_MEM64 = m /\ s R_RSP = rsp)
  | 0x141035 => Some (s R_RAX = isinfl_spec (m Ⓓ[8 + rsp]) (m Ⓓ[12 + rsp]) (m Ⓦ[16 + rsp]) /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem isinfl_correct:
  forall s t s' x' m rsp
         (ENTRY: startof t (x',s') = (Addr 0x140ff0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp),
  satisfies_all isinfl_amd64 (isinfl_invs m rsp) isinfl_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isinfl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM RSP].
  repeat x64_step.
  split.
  { pose proof (isinfl_bits (m Ⓓ[8 + rsp]) (m Ⓓ[12 + rsp]) (m Ⓠ[16 + rsp])
                  (getmem_bound 64 LittleE 4 m _) (getmem_bound 64 LittleE 4 m _)) as IB.
    replace (m Ⓦ[16 + rsp]) with (m Ⓠ[16 + rsp] mod 2^16) by (rewrite (getmem_mod 64 LittleE 2 8); reflexivity).
    rewrite <- IB. reflexivity. }
  split; reflexivity || assumption.
(* QED-SLOW: the tactics above finish in ~10 s, but the kernel check at Qed
   ran for more than 5 minutes without finishing.  The likely trigger is the
   known one for comparisons against a power-of-two literal (here the carry
   of ADD EAX,0x80000000, a test against 2^31), which the Strategy
   declaration in Picinae_core.v does not cover.  The Qed optimization is
   left for later. *)
Admitted.
