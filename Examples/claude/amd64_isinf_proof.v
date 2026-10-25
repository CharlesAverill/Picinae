(* isinf -- test for infinity

   SEMANTICS
   ---------
   isinf(x) returns 1 if x is +inf, -1 if x is -inf, and 0 otherwise.
   glibc works on the bit pattern of the double in XMM0 without branches:
   with a = bits & ~sign and D = a ^ 0x7ff0000000000000 (zero exactly for
   +-inf), it computes ~((-D | D) >>s 63) & (bits >>s 62).  The first factor
   is all ones when D = 0 and zero otherwise; the second is 1 for +inf and
   -1 for -inf.

   SPECIFICATION (man 3 isinf, Linux man-pages 5.10, Ubuntu 22.04)
   ----------------------------------------------------------------

     int isinf(double x);

     isinf() returns 1 if x is positive infinity, and -1 if x is negative
     infinity.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol isinf at 0x141390 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isinf_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x; its low 64 bits are the binary64 pattern.
   Output:  RAX (an int, zero-extended) is 1 if x = +inf, 0xffffffff (-1) if
            x = -inf, and 0 otherwise.  RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import isinf_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem isinf_nwc: forall s2 s1, isinf_amd64 s1 = isinf_amd64 s2.
Proof. reflexivity. Qed.

Theorem isinf_welltyped: welltyped_prog x64typctx isinf_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isinf_preserves_memory:
  forall_endstates isinf_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isinf_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isinf_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition INF64 := 0x7ff0000000000000.

(* The result: 1 for +inf, -1 (as a 32-bit int) for -inf, else 0. *)
Definition isinf_spec (x:N) :=
  if x mod 2^63 =? INF64 then (if N.testbit x 63 then 2^32 - 1 else 1) else 0.

(* -D | D has its sign bit set exactly when D is nonzero. *)
Lemma neg_or_sign: forall D, D < 2^63 -> N.testbit (msub 64 0 D .| D) 63 = negb (D =? 0).
Proof.
  intros D DB. rewrite N.lor_spec. destruct (N.eqb_spec D 0) as [Z|Z].
  - subst D. reflexivity.
  - assert (E: msub 64 0 D = 2^64 - D).
    { rewrite msub_wrap by (rewrite N.mod_0_l, N.mod_small; lia).
      rewrite N.mod_0_l, N.mod_small by lia. lia. }
    rewrite E. replace (N.testbit D 63) with false.
    + rewrite Bool.orb_false_r. cbn [negb].
      change (2^64) with 18446744073709551616 in *. change (2^63) with 9223372036854775808 in *.
      rewrite N.testbit_eqb. rewrite N.eqb_eq.
      replace (18446744073709551616 - D) with (9223372036854775808 + (9223372036854775808 - D)) by lia.
      rewrite <- (N.mul_1_l 9223372036854775808) at 1. change 9223372036854775808 with (2^63).
      rewrite N.div_add_l by discriminate. rewrite N.div_small by (change (2^63) with 9223372036854775808; lia).
      reflexivity.
    + symmetry. apply N.bits_above_log2. apply N.log2_lt_pow2. lia. exact DB.
Qed.

Lemma isinf_bits:
  forall x,
  (N.lnot ((0 ⊖ (x mod 2^63 .^ INF64) .| x mod 2^63 .^ INF64) >>> (63 .& 63)) 32 .& x >>> (62 .& 63))
    mod 2^32 = isinf_spec x.
Proof.
  intro x. change (63 .& 63) with 63. change (62 .& 63) with 62.
  set (D := x mod 2^63 .^ INF64).
  assert (DB: D < 2^63) by (apply lxor_bound; [apply N.mod_lt; discriminate | reflexivity]).
  assert (V: N.testbit (msub 64 0 D .| D) 63 = negb (D =? 0)) by (apply neg_or_sign, DB).
  assert (DZ: (D =? 0) = (x mod 2^63 =? INF64)).
  { unfold D. destruct (N.eqb_spec (x mod 2^63) INF64) as [E|E].
    - rewrite E, N.lxor_nilpotent. reflexivity.
    - apply N.eqb_neq. intro H. apply E. apply N.lxor_eq, H. }
  unfold isinf_spec. rewrite <- DZ.
  apply N.bits_inj. intro i.
  destruct (N.ltb_spec i 32) as [I|I].
  - rewrite N.mod_pow2_bits_low by exact I. rewrite N.land_spec, N.lnot_spec_low by exact I.
    rewrite !ashiftr_spec. replace (i <? 64) with true by (symmetry; apply N.ltb_lt; lia).
    replace (N.min (i + 63) (N.pred 64)) with 63 by lia. rewrite V. cbn [andb].
    destruct (D =? 0); cbn [negb andb].
    + symmetry in DZ. apply N.eqb_eq in DZ.
      destruct (N.eqb_spec i 0) as [->|I0].
      * replace (N.min (0 + 62) (N.pred 64)) with 62 by reflexivity.
        replace (N.testbit x 62) with true.
        destruct (N.testbit x 63); reflexivity.
        rewrite <- (N.mod_pow2_bits_low x 63 62) by lia. rewrite DZ. reflexivity.
      * replace (N.min (i + 62) (N.pred 64)) with 63 by lia.
        destruct (N.testbit x 63).
        -- symmetry. change (2^32 - 1) with (N.ones 32). apply N.ones_spec_low. exact I.
        -- symmetry. destruct i as [|p]. contradiction. destruct p; reflexivity.
    + symmetry. apply N.bits_0.
  - rewrite N.mod_pow2_bits_high by exact I.
    destruct (D =? 0); [destruct (N.testbit x 63)|]; symmetry;
      try apply N.bits_0; apply N.bits_above_log2; cbn; lia.
Qed.

(* An arithmetic shift reads only the low 64 bits. *)
Lemma ashiftr_mod: forall w x k, ashiftr w (x mod 2^w) k = ashiftr w x k.
Proof.
  intros w x k. apply N.bits_inj. intro i. rewrite !ashiftr_spec.
  destruct (N.ltb_spec i w); [|reflexivity]. cbn [andb].
  rewrite N.mod_pow2_bits_low by lia. reflexivity.
Qed.

Definition isinf_exit (t:trace) :=
  match t with (Addr 0x1413c5,_)::_ => true | _ => false end.

Definition isinf_invs (m:memory) (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x141390 => Some (s R_YMM0 = x /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 0x1413c5 => Some (s R_RAX = isinf_spec x /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem isinf_correct:
  forall s t s' x' m x rsp
         (ENTRY: startof t (x',s') = (Addr 0x141390, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x) (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp),
  satisfies_all isinf_amd64 (isinf_invs m x rsp) isinf_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isinf_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [MEM RSP]].
  repeat x64_step.
  rewrite ?ashiftr_mod. split. apply isinf_bits. split; first [reflexivity | assumption].
Qed.
