(* abs -- absolute value of an int

   SEMANTICS
   ---------
   abs returns the absolute value of its 32-bit signed argument.  glibc computes
   -j with NEG and keeps j instead (CMOVS) when -j is negative.  For j = INT_MIN,
   where the C result is undefined, -j wraps back to INT_MIN, so abs returns
   INT_MIN.

   SPECIFICATION (man 3 abs, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            int abs(int j);

     DESCRIPTION
            The  abs() function computes the absolute value of the integer argument
            j.

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
            symbol abs at 0x145dd0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see abs_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI (low 32 bits of RDI) holds j, read as a 32-bit two's-complement int.
   Output:  On return, RAX = |j| mod 2^32 (zero-extended to 64 bits).  This holds
            for every j, including INT_MIN, where the bit pattern 2^31 is INT_MIN
            again.  Corollary (abs_value): if j <> INT_MIN, then EAX read as a
            signed int is exactly |j|.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import abs_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem abs_nwc: forall s2 s1, abs_amd64 s1 = abs_amd64 s2.
Proof. reflexivity. Qed.

Theorem abs_welltyped: welltyped_prog x64typctx abs_amd64.
Proof. Picinae_typecheck. Qed.

Theorem abs_preserves_memory:
  forall_endstates abs_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem abs_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates abs_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 11. *)
Definition abs_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 11 => true
  | _ => false
  end | _ => false end.

Definition postcondition (j:Z) (rsp:N) (s:store) :=
  s R_RAX = ofZ 32 (Z.abs j) /\ s R_RSP = rsp.

Definition abs_invs (j:Z) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_RDI) = j /\ s R_RSP = rsp)
  | 11 => Some (postcondition j rsp s)
  | _ => None
  end | _ => None end.

Lemma abs_math:
  forall n, let j := toZ 32 n in
  (slt 32 (msub 32 0 n) 0 = true -> n mod 2^32 = ofZ 32 (Z.abs j)) /\
  (slt 32 (msub 32 0 n) 0 = false -> msub 32 0 n = ofZ 32 (Z.abs j)).
Proof.
  intros n j.
  assert (V: msub 32 0 n = ofZ 32 (- j)) by (rewrite msub_sbop; reflexivity).
  assert (TV: toZ 32 (msub 32 0 n) = canonicalZ 32 (- j)) by (rewrite toZ_msub; reflexivity).
  assert (N: n mod 2^32 = ofZ 32 j) by (symmetry; apply ofZ_toZ_bitcast; reflexivity).
  unfold slt. rewrite TV. change (toZ 32 0) with 0%Z.
  pose proof (toZ32_range n) as R. fold j in R.
  destruct (Z.lt_trichotomy j 0) as [NEG|[Z0|POS]].
    destruct (Z.eq_dec j (-2^31)) as [MIN|NMIN].
      rewrite MIN. split; intro BC. rewrite N, MIN. reflexivity. discriminate BC.
      rewrite (canonicalZ_id 32) by (unfold signed_range; simpl; lia).
      replace (- j <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      split; intro BC. discriminate BC. rewrite V, Z.abs_neq by lia. reflexivity.
    rewrite Z0. split; intro BC. discriminate BC. rewrite V, Z0. reflexivity.
    rewrite (canonicalZ_id 32) by (unfold signed_range; simpl; lia).
    replace (- j <? 0)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    split; intro BC. rewrite N, Z.abs_eq by lia. reflexivity. discriminate BC.
Qed.

Theorem abs_correct:
  forall s t s' x' j rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (J: toZ 32 (s R_RDI) = j) (RSP: s R_RSP = rsp),
  satisfies_all abs_amd64 (abs_invs j rsp) abs_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply abs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [J RSP].
  repeat x64_step.
  all: assert (HZ: s1 R_RDI mod 2^32 >> 32 = 0) by
         (rewrite N.shiftr_div_pow2; apply N.div_small, mp2_mod_lt).
  all: rewrite HZ, !N.shiftr_0_r, N.Div0.mod_0_l, N.shiftl_0_l, N.lor_0_l,
               mp2_mod_mod, msub_mod_r, (N.mod_small (msub _ _ _)) in BC
         by (discriminate || apply msub_lt).
  all: split; [|assumption]; subst j.
    apply abs_math. assumption.
    apply abs_math. assumption.
Qed.

(* For every j other than INT_MIN, the returned int is exactly |j|. *)
Theorem abs_value:
  forall j, (-2^31 < j < 2^31)%Z -> toZ 32 (ofZ 32 (Z.abs j)) = Z.abs j.
Proof.
  intros j R. rewrite toZ_ofZ_canonicalZ by reflexivity.
  apply (canonicalZ_id 32). reflexivity. unfold signed_range. simpl. lia.
Qed.
