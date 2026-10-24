(* div -- quotient and remainder of an int division

   SEMANTICS
   ---------
   div divides two 32-bit signed integers and returns the quotient (rounded
   toward zero) and the remainder, which satisfy quot*denominator + rem =
   numerator.  glibc sign-extends the numerator into EDX:EAX (CDQ), uses IDIV,
   and packs the 8-byte div_t result into RAX through XMM0/XMM1 (MOVD,
   PUNPCKLDQ, MOVQ).

   SPECIFICATION (man 3 ldiv, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            div_t div(int numerator, int denominator);

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

     (glibc's <stdlib.h> declares div_t as struct { int quot; int rem; }.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol div at 0x145e00 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see div_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI holds the numerator n and ESI the denominator d, both read as
            32-bit two's-complement ints.
   Precondition:  d <> 0, and not (n = INT_MIN and d = -1).  These are exactly
            the inputs whose quotient is undefined in C, and the ones on which
            IDIV raises #DE in hardware.  Ghidra's p-code for IDIV does not model
            #DE, so the lifted program says nothing useful about them.
   Output:  div_t is an 8-byte struct, so it is returned in RAX: quot in bits
            0-31 and rem in bits 32-63.  On return,
              bits 0-31 of RAX read as a signed int  = Z.quot n d  (rounded toward zero),
              bits 32-63 of RAX read as a signed int = Z.rem n d,
            so quot*d + rem = n holds exactly (div_identity).  XMM0 and XMM1 are
            clobbered; both are caller-saved.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import div_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem div_nwc: forall s2 s1, div_amd64 s1 = div_amd64 s2.
Proof. reflexivity. Qed.

Theorem div_welltyped: welltyped_prog x64typctx div_amd64.
Proof. Picinae_typecheck. Qed.

Theorem div_preserves_memory:
  forall_endstates div_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem div_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates div_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 26. *)
Definition div_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 26 => true
  | _ => false
  end | _ => false end.

Definition postcondition (n d:Z) (rsp:N) (s:store) :=
  toZ 32 (s R_RAX mod 2^32) = Z.quot n d /\ toZ 32 (s R_RAX >> 32) = Z.rem n d /\ s R_RSP = rsp.

Definition div_invs (n d:Z) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_RDI) = n /\ toZ 32 (s R_RSI) = d /\ s R_RSP = rsp)
  | 26 => Some (postcondition n d rsp s)
  | _ => None
  end | _ => None end.

Theorem div_correct:
  forall s t s' x' n d rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (HN: toZ 32 (s R_RDI) = n) (HD: toZ 32 (s R_RSI) = d) (RSP: s R_RSP = rsp)
         (DNZ: d <> 0%Z) (NOVF: ~ (n = (-2^31)%Z /\ d = (-1)%Z)),
  satisfies_all div_amd64 (div_invs n d rsp) div_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply div_welltyped. intro MDL1.
  clear - PRE MDL1 DNZ NOVF. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [HN [HD RSP]].
  repeat x64_step.
  rewrite !N.shiftr_0_r, !mp2_mod_mod.
  rewrite (recombine 32 64 (scast 32 64 (s1 R_RDI mod 2^32)) (s1 R_RDI mod 2^32))
    by (reflexivity || apply ofZ_bound ||
        (rewrite scast_low by discriminate; apply mp2_mod_mod)).
  rewrite packed_hi by (reflexivity || apply mp2_mod_lt).
  unfold sbop2. rewrite !toZ_scast, !ofZ_mod_narrow by first [reflexivity | discriminate].
  rewrite !toZ_mod_pow2, HN, HD by discriminate.
  pose proof (toZ32_range (s1 R_RDI)) as RN. pose proof (toZ32_range (s1 R_RSI)) as RD.
  rewrite HN in RN. rewrite HD in RD.
  rewrite !toZ_ofZ_canonicalZ by reflexivity.
  rewrite !(canonicalZ_id 32) by (reflexivity ||
    (unfold signed_range; simpl;
     first [ apply (quot_range n d (2^31)); lia | apply (rem_range n d (2^31)); lia ])).
  repeat split. assumption.
Qed.
