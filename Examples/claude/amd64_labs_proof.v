(* labs -- absolute value of a long

   SEMANTICS
   ---------
   labs returns the absolute value of its 64-bit signed argument.  glibc computes
   -j with NEG and keeps j instead (CMOVS) when -j is negative.  For j = LONG_MIN,
   where the C result is undefined, -j wraps back to LONG_MIN, so labs returns
   LONG_MIN.  On amd64, long, long long and intmax_t are all 64 bits.  In this
   libc, llabs (0x145df0) is byte-for-byte identical code, and imaxabs is an
   alias of labs (same address), so this proof covers all three.

   SPECIFICATION (man 3 abs, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            long labs(long j);
            long long llabs(long long j);

            #include <inttypes.h>
            intmax_t imaxabs(intmax_t j);

     DESCRIPTION
            The labs(), llabs(), and imaxabs() functions compute  the  absolute
            value  of  the argument j of the appropriate integer type for the func-
            tion.

     RETURN VALUE
            Returns the absolute value of the integer argument, of the  appropriate
            integer type for the function.

     NOTES
            Trying  to  take the absolute value of the most negative integer is not
            defined.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol labs at 0x145de0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see labs_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI holds j, read as a 64-bit two's-complement long.
   Output:  On return, RAX = |j| mod 2^64.  This holds for every j, including
            LONG_MIN, where the bit pattern 2^63 is LONG_MIN again.
            Corollary (labs_value): if j <> LONG_MIN, then RAX read as a signed
            long is exactly |j|.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import labs_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem labs_nwc: forall s2 s1, labs_amd64 s1 = labs_amd64 s2.
Proof. reflexivity. Qed.

Theorem labs_welltyped: welltyped_prog x64typctx labs_amd64.
Proof. Picinae_typecheck. Qed.

Theorem labs_preserves_memory:
  forall_endstates labs_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem labs_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates labs_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 14. *)
Definition labs_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 14 => true
  | _ => false
  end | _ => false end.

Definition postcondition (j:Z) (rsp:N) (s:store) :=
  s R_RAX = ofZ 64 (Z.abs j) /\ s R_RSP = rsp.

Definition labs_invs (j:Z) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 64 (s R_RDI) = j /\ s R_RSP = rsp)
  | 14 => Some (postcondition j rsp s)
  | _ => None
  end | _ => None end.

Lemma labs_math:
  forall n, let j := toZ 64 n in
  (slt 64 (msub 64 0 n) 0 = true -> n mod 2^64 = ofZ 64 (Z.abs j)) /\
  (slt 64 (msub 64 0 n) 0 = false -> msub 64 0 n = ofZ 64 (Z.abs j)).
Proof.
  intros n j.
  assert (V: msub 64 0 n = ofZ 64 (- j)) by (rewrite msub_sbop; reflexivity).
  assert (TV: toZ 64 (msub 64 0 n) = canonicalZ 64 (- j)) by (rewrite toZ_msub; reflexivity).
  assert (N: n mod 2^64 = ofZ 64 j) by (symmetry; apply ofZ_toZ_bitcast; reflexivity).
  unfold slt. rewrite TV. change (toZ 64 0) with 0%Z.
  pose proof (toZ64_range n) as R. fold j in R.
  destruct (Z.lt_trichotomy j 0) as [NEG|[Z0|POS]].
    destruct (Z.eq_dec j (-2^63)) as [MIN|NMIN].
      rewrite MIN. split; intro BC. rewrite N, MIN. reflexivity. discriminate BC.
      rewrite (canonicalZ_id 64) by (unfold signed_range; simpl; lia).
      replace (- j <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      split; intro BC. discriminate BC. rewrite V, Z.abs_neq by lia. reflexivity.
    rewrite Z0. split; intro BC. discriminate BC. rewrite V, Z0. reflexivity.
    rewrite (canonicalZ_id 64) by (unfold signed_range; simpl; lia).
    replace (- j <? 0)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    split; intro BC. rewrite N, Z.abs_eq by lia. reflexivity. discriminate BC.
Qed.

Theorem labs_correct:
  forall s t s' x' j rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (J: toZ 64 (s R_RDI) = j) (RSP: s R_RSP = rsp),
  satisfies_all labs_amd64 (labs_invs j rsp) labs_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply labs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [J RSP].
  repeat x64_step.
  all: split; [|assumption]; subst j.
    rewrite <- (N.mod_small (s1 R_RDI) (2^64)) at 1 by apply (MDL1 R_RDI 64), eq_refl.
    apply labs_math. assumption.
    apply labs_math. assumption.
Qed.

(* For every j other than LONG_MIN, the returned long is exactly |j|. *)
Theorem labs_value:
  forall j, (-2^63 < j < 2^63)%Z -> toZ 64 (ofZ 64 (Z.abs j)) = Z.abs j.
Proof.
  intros j R. rewrite toZ_ofZ_canonicalZ by reflexivity.
  apply (canonicalZ_id 64). reflexivity. unfold signed_range. simpl. lia.
Qed.
