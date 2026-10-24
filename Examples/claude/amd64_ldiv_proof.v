(* ldiv -- quotient and remainder of a long division

   SEMANTICS
   ---------
   ldiv divides two 64-bit signed integers and returns the quotient (rounded
   toward zero) and the remainder, which satisfy quot*denominator + rem =
   numerator.  glibc sign-extends the numerator into RDX:RAX (CQO) and uses
   IDIV.  On amd64, long, long long and intmax_t are all 64 bits.  In this libc,
   lldiv (0x145e30) is byte-for-byte identical code, and imaxdiv is an alias of
   ldiv (same address), so this proof covers all three.

   SPECIFICATION (man 3 ldiv, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            ldiv_t ldiv(long numerator, long denominator);
            lldiv_t lldiv(long long numerator, long long denominator);

            #include <inttypes.h>
            imaxdiv_t imaxdiv(intmax_t numerator, intmax_t denominator);

     DESCRIPTION
            The div() function computes the value numerator/denominator and returns
            the quotient and remainder in a structure named div_t that contains two
            integer members (in unspecified order) named quot and  rem.   The  quo-
            tient  is  rounded  toward  zero.   The result satisfies quot*denomina-
            tor+rem = numerator.

            The ldiv(), lldiv(), and imaxdiv() functions do the same, dividing num-
            bers  of  the indicated type and returning the result in a structure of
            the indicated name, in all cases with fields quot and rem of the  same
            type as the function arguments.

     RETURN VALUE
            The div_t (etc.) structure.

     (glibc's <stdlib.h> declares ldiv_t as struct { long quot; long rem; }.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol ldiv at 0x145e20 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see ldiv_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI holds the numerator n and RSI the denominator d, both read as
            64-bit two's-complement longs.
   Precondition:  d <> 0, and not (n = LONG_MIN and d = -1).  These are exactly
            the inputs whose quotient is undefined in C, and the ones on which
            IDIV raises #DE in hardware.  Ghidra's p-code for IDIV does not model
            #DE, so the lifted program says nothing useful about them.
   Output:  ldiv_t is a 16-byte struct of two INTEGER-class fields, so it is
            returned in RAX (quot) and RDX (rem).  On return,
              RAX read as a signed long = Z.quot n d   (rounded toward zero),
              RDX read as a signed long = Z.rem n d,
            so quot*d + rem = n holds exactly (ldiv_identity).
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import ldiv_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem ldiv_nwc: forall s2 s1, ldiv_amd64 s1 = ldiv_amd64 s2.
Proof. reflexivity. Qed.

Theorem ldiv_welltyped: welltyped_prog x64typctx ldiv_amd64.
Proof. Picinae_typecheck. Qed.

Theorem ldiv_preserves_memory:
  forall_endstates ldiv_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ldiv_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates ldiv_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 12. *)
Definition ldiv_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 12 => true
  | _ => false
  end | _ => false end.

Definition postcondition (n d:Z) (rsp:N) (s:store) :=
  toZ 64 (s R_RAX) = Z.quot n d /\ toZ 64 (s R_RDX) = Z.rem n d /\ s R_RSP = rsp.

Definition ldiv_invs (n d:Z) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 64 (s R_RDI) = n /\ toZ 64 (s R_RSI) = d /\ s R_RSP = rsp)
  | 12 => Some (postcondition n d rsp s)
  | _ => None
  end | _ => None end.

Theorem ldiv_correct:
  forall s t s' x' n d rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (HN: toZ 64 (s R_RDI) = n) (HD: toZ 64 (s R_RSI) = d) (RSP: s R_RSP = rsp)
         (DNZ: d <> 0%Z) (NOVF: ~ (n = (-2^63)%Z /\ d = (-1)%Z)),
  satisfies_all ldiv_amd64 (ldiv_invs n d rsp) ldiv_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ldiv_welltyped. intro MDL1.
  clear - PRE MDL1 DNZ NOVF. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [HN [HD RSP]].
  repeat x64_step.
  assert (RDI64: s1 R_RDI < 2^64) by apply (MDL1 R_RDI 64), eq_refl.
  rewrite (recombine 64 128 (scast 64 128 (s1 R_RDI)) (s1 R_RDI))
    by (reflexivity || apply ofZ_bound || (rewrite scast_low by discriminate; apply N.mod_small, RDI64)).
  unfold sbop2. rewrite !toZ_scast, !ofZ_mod_narrow, HN, HD by first [reflexivity | discriminate].
  pose proof (toZ64_range (s1 R_RDI)) as RN. pose proof (toZ64_range (s1 R_RSI)) as RD.
  rewrite HN in RN. rewrite HD in RD.
  rewrite !toZ_ofZ_canonicalZ by reflexivity.
  rewrite !(canonicalZ_id 64) by (reflexivity ||
    (unfold signed_range; simpl;
     first [ apply (quot_range n d (2^63)); lia | apply (rem_range n d (2^63)); lia ])).
  repeat split. assumption.
Qed.

(* The man page's identity: quot*denominator + rem = numerator. *)
Theorem ldiv_identity:
  forall n d (s:store), postcondition n d (s R_RSP) s ->
  Z.add (Z.mul (toZ 64 (s R_RAX)) d) (toZ 64 (s R_RDX)) = n.
Proof.
  intros n d s [Q [R _]]. rewrite Q, R, Z.mul_comm. symmetry. apply Z.quot_rem'.
Qed.
