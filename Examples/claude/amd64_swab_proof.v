(* swab -- swap adjacent bytes

   SEMANTICS
   ---------
   swab(from, to, n) copies the first n bytes of from to to with each adjacent
   pair of bytes swapped: to[2i] = from[2i+1] and to[2i+1] = from[2i].  glibc
   rounds n down to an even number (n & ~1) and does nothing if the result is
   <= 1 as a signed value, which covers n negative, 0 or 1.  It copies the
   pairs from the last one back to the first.  When n is odd, glibc's
   "something unspecified with the last byte" is in fact nothing: the last
   byte is never written.

   SPECIFICATION (man 3 swab, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #define _XOPEN_SOURCE       /* See feature_test_macros(7) */
            #include <unistd.h>
            void swab(const void *from, void *to, ssize_t n);

     DESCRIPTION
            The swab() function copies n bytes from the array pointed to by from to
            the array pointed to by to, exchanging adjacent  even  and  odd  bytes.
            This  function is used to exchange data between machines that have dif-
            ferent low/high byte ordering.

            This function does nothing when n is negative.  When n is positive  and
            odd, it handles n-1 bytes as above, and does something unspecified with
            the last byte.  (In other words, n should be even.)

     RETURN VALUE
            The swab() function returns no value.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol swab at 0x1aa700 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see swab_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = from, RSI = to (pointers), RDX = n (ssize_t, 64-bit signed);
            m = memory on entry.  Let n2 = n & ~1, and let len = n2 if n2 > 1
            (signed), else len = 0.
   Precondition:  no byte of from[0, len) lies in to[0, len).  (The man page
            doesn't say what happens when the arrays overlap.  glibc reads each
            source pair just before writing the destination pair, so for
            overlapping arrays the result depends on the copy order.)
   Output:  swab returns void.  On return, for every i with 2i+1 < len,
              m'[to+2i] = m[from+2i+1]  and  m'[to+2i+1] = m[from+2i],
            and every byte outside to[0, len) is unchanged.  In particular,
            memory is unchanged when n <= 1, and to[n-1] is not written when n
            is odd.  Addresses are taken mod 2^64.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import swab_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem swab_nwc: forall s2 s1, swab_amd64 s1 = swab_amd64 s2.
Proof. reflexivity. Qed.

Theorem swab_welltyped: welltyped_prog x64typctx swab_amd64.
Proof. Picinae_typecheck. Qed.

Theorem swab_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates swab_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 38; the loop head is at offset 16. *)
Definition swab_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 38 => true
  | _ => false
  end | _ => false end.

Definition swab_len (n:N) :=
  let n2 := N.land n 18446744073709551614 in
  if Z.leb (toZ 64 n2) 1 then 0 else n2.

(* Pairs at offsets [j, len) are done, and nothing outside to[j, len) changed. *)
Definition swab_done (m m':memory) (from to j len:N) :=
  (forall i, j <= 2*i -> 2*i+1 < len ->
     m' Ⓑ[to ⊕ 2*i] = m Ⓑ[from ⊕ (2*i+1)] /\ m' Ⓑ[to ⊕ (2*i+1)] = m Ⓑ[from ⊕ 2*i]) /\
  (forall a, ~ (j <= msub 64 a to < len) -> m' Ⓑ[a] = m Ⓑ[a]).

Lemma swab_len_lt: forall n, swab_len n < 2^63.
Proof.
  intro n. unfold swab_len.
  assert (X64: n .& 18446744073709551614 < 2^64).
    eapply N.le_lt_trans. apply N.land_le_r. reflexivity.
  destruct (Z.leb (toZ 64 (n .& 18446744073709551614)) 1) eqn:LE. reflexivity.
  rewrite toZ64_le1 in LE by assumption. apply Bool.orb_false_iff in LE.
  destruct LE as [_ LE]. apply N.leb_gt in LE. assumption.
Qed.

Lemma swab_step:
  forall m mm from to j len,
  2 <= j -> j <= len -> len < 2^63 -> j mod 2 = 0 ->
  (forall i, i < len -> ~ (msub 64 (from ⊕ i) to < len)) ->
  swab_done m mm from to j len ->
  swab_done m (mm [Ⓑ msub 64 (to + j) 2 := mm Ⓑ[msub 64 from 1 + j]]
                  [Ⓑ msub 64 to 1 + j := mm Ⓑ[msub 64 (from + j) 2]])
            from to (j - 2) len.
Proof.
  intros m mm from to j len J2 JL LEN EV NOV [PAIRS FRAME].
  (* the two source bytes still hold their original values *)
  assert (S1: mm Ⓑ[msub 64 from 1 + j] = m Ⓑ[from ⊕ (j-1)]).
    rewrite <- getmem_mod_l. replace ((msub 64 from 1 + j) mod 2^64) with (from ⊕ (j-1)) by mlia.
    apply FRAME. intro H. apply (NOV (j-1)). lia. lia.
  assert (S0: mm Ⓑ[msub 64 (from + j) 2] = m Ⓑ[from ⊕ (j-2)]).
    rewrite <- getmem_mod_l. replace (msub 64 (from + j) 2 mod 2^64) with (from ⊕ (j-2)) by mlia.
    apply FRAME. intro H. apply (NOV (j-2)). lia. lia.
  rewrite S1, S0. split.
  - intros i I1 I2. rewrite !getmem1_setmem1.
    assert (B1: m Ⓑ[from ⊕ (j-1)] < 2^8) by apply getmem_bound.
    assert (B0: m Ⓑ[from ⊕ (j-2)] < 2^8) by apply getmem_bound.
    destruct (N.eq_dec (2*i) (j-2)) as [E|NE].
    + rewrite E.
      replace ((to ⊕ (j-2)) mod 2^64 =? (msub 64 to 1 + j) mod 2^64) with false by (symmetry; apply N.eqb_neq; mlia).
      replace ((to ⊕ (j-2)) mod 2^64 =? msub 64 (to + j) 2 mod 2^64) with true by (symmetry; apply N.eqb_eq; mlia).
      replace ((to ⊕ (j-2+1)) mod 2^64 =? (msub 64 to 1 + j) mod 2^64) with true by (symmetry; apply N.eqb_eq; mlia).
      rewrite (N.mod_small (m Ⓑ[from ⊕ (j-1)])), (N.mod_small (m Ⓑ[from ⊕ (j-2)])) by assumption.
      replace (j-2+1) with (j-1) by lia. split; reflexivity.
    + assert (I3: j <= 2*i) by lia.
      replace ((to ⊕ 2*i) mod 2^64 =? (msub 64 to 1 + j) mod 2^64) with false by (symmetry; apply N.eqb_neq; mlia).
      replace ((to ⊕ 2*i) mod 2^64 =? msub 64 (to + j) 2 mod 2^64) with false by (symmetry; apply N.eqb_neq; mlia).
      replace ((to ⊕ (2*i+1)) mod 2^64 =? (msub 64 to 1 + j) mod 2^64) with false by (symmetry; apply N.eqb_neq; mlia).
      replace ((to ⊕ (2*i+1)) mod 2^64 =? msub 64 (to + j) 2 mod 2^64) with false by (symmetry; apply N.eqb_neq; mlia).
      apply PAIRS; assumption.
  - intros a NA. rewrite !getmem1_setmem1.
    replace (a mod 2^64 =? (msub 64 to 1 + j) mod 2^64) with false.
    replace (a mod 2^64 =? msub 64 (to + j) 2 mod 2^64) with false.
    apply FRAME. intro H. apply NA. lia.
    symmetry. apply N.eqb_neq. intro E. apply NA. rewrite (msub_add_l a to (j-2)); [lia|lia|]. rewrite E. mlia.
    symmetry. apply N.eqb_neq. intro E. apply NA. rewrite (msub_add_l a to (j-1)); [lia|lia|]. rewrite E. mlia.
Qed.

Definition postcondition (m from to n rsp:N) (s:store) :=
  swab_done m (s V_MEM64) from to 0 (swab_len n) /\ s R_RSP = rsp.

Definition swab_invs (m from to n rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = from /\ s R_RSI = to /\ s R_RDX = n /\
               s R_RSP = rsp)
  | 16 => Some (s R_RDI = from /\ s R_RSI = to /\ s R_RSP = rsp /\
                exists j, s R_RDX = j /\ j mod 2 = 0 /\ 2 <= j <= swab_len n /\
                          swab_done m (s V_MEM64) from to j (swab_len n))
  | 38 => Some (postcondition m from to n rsp s)
  | _ => None
  end | _ => None end.

Theorem swab_correct:
  forall s t s' x' m from to n rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (FROM: s R_RDI = from) (TO: s R_RSI = to)
         (NN: s R_RDX = n) (RSP: s R_RSP = rsp)
         (NOV: forall i, i < swab_len n -> ~ (msub 64 (from ⊕ i) to < swab_len n)),
  satisfies_all swab_amd64 (swab_invs m from to n rsp) swab_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply swab_welltyped. intro MDL1.
  clear - PRE MDL1 NOV. rename t1 into t.
  destruct_inv 64 PRE.

  - (* entry *)
    destruct PRE as [MEM [FROM [TO [NN RSP]]]].
    assert (X64: n .& 18446744073709551614 < 2^64).
      eapply N.le_lt_trans. apply N.land_le_r. reflexivity.
    assert (XE: (n .& 18446744073709551614) mod 2 = 0).
      rewrite <- (N.land_ones _ 1), <- N.land_assoc. apply N.land_0_r.
    repeat x64_step.
    + rewrite cmp1_jle in BC by assumption.
      destruct (Z.leb (toZ 64 (n .& 18446744073709551614)) 1) eqn:LE; [discriminate|].
      assert (SL: swab_len n = n .& 18446744073709551614) by (unfold swab_len; rewrite LE; reflexivity).
      rewrite toZ64_le1 in LE by assumption. apply Bool.orb_false_iff in LE.
      destruct LE as [LE1 LE2]. apply N.ltb_ge in LE1.
      repeat split; try assumption. exists (n .& 18446744073709551614).
      rewrite SL, MEM. repeat split; try assumption; try lia.
    + rewrite cmp1_jle in BC by assumption.
      destruct (Z.leb (toZ 64 (n .& 18446744073709551614)) 1) eqn:LE; [|discriminate].
      assert (SL: swab_len n = 0) by (unfold swab_len; rewrite LE; reflexivity).
      rewrite SL, MEM. repeat split; try assumption; try lia.

  - (* loop *)
    destruct PRE as [FROM [TO [RSP [j [RDX [EVEN [J DONE]]]]]]].
    pose proof (swab_len_lt n) as LEN.
    repeat x64_step.
    + split; [|assumption]. apply N.eqb_eq in BC.
      replace 0 with (j - 2) by lia. subst j. apply swab_step; first [assumption | lia].
    + apply N.eqb_neq in BC.
      split; [reflexivity|split; [reflexivity|split; [assumption|]]].
      exists (j - 2). split; [mlia|]. split; [lia|]. split; [lia|].
      apply swab_step; first [assumption | lia].
Qed.
