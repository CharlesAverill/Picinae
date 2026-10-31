(* isinf (AArch64 / ARMv8) -- test whether a double is infinite.

   SEMANTICS
   ---------
   isinf(x) returns 1 if x is +inf, -1 if x is -inf, and 0 otherwise.  The code
   is branch-free: it isolates |x|, XORs with the +inf bit pattern (zero iff x is
   an infinity), uses the sign of (-D | D) to build an all-ones "not infinity"
   mask, and ANDs that (complemented, via `bic`) against the arithmetic-shift of
   the raw bits (which is 0b01 = 1 for +inf and all-ones = -1 for -inf).  The
   specification isinf_spec is identical to the amd64 proof.

     `fmov x0,d0; and x2,x0,#0x7fffffffffffffff; asr x0,x0,#0x3e;
      eor x2,x2,#0x7ff0000000000000; neg x1,x2; orr x1,x1,x2; asr x1,x1,#0x3f;
      bic w0,w0,w1; ret`

   SPECIFICATION (man 3 isinf)
   ---------------------------
     int isinf(double x);
     isinf() returns 1 if x is positive infinity, and -1 if x is negative
     infinity.

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
            symbol isinf at 0x139ed0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Model:   Specification and proof written by Claude Opus 4.8 (claude-opus-4-8),
            an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   D0 (low 64 bits of the SIMD register Z0) holds the double's bits.
   Output:  W0 = 1 (+inf), 0xffffffff (-1, as a 32-bit int) for -inf, else 0.
            Memory is unchanged (leaf function, returns via X30).
 *)

Require Import Picinae_armv8.
Require Import isinf_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem isinf_nwc: forall s2 s1, isinf_arm8 s1 = isinf_arm8 s2.
Proof. reflexivity. Qed.
Theorem isinf_welltyped: welltyped_prog arm8typctx isinf_arm8.
Proof. Picinae_typecheck. Qed.
Theorem isinf_preserves_memory:
  forall_endstates isinf_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition INF64 := 9218868437227405312.  (* 0x7ff0000000000000 *)

(* 1 for +inf, -1 (as a 32-bit int) for -inf, else 0.  Same spec as amd64. *)
Definition isinf_spec (z:N) :=
  if z mod 2^63 =? INF64 then (if N.testbit z 63 then 2^32 - 1 else 1) else 0.

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

(* An arithmetic shift reads only the low 64 bits. *)
Lemma ashiftr_mod: forall w x k, ashiftr w (x mod 2^w) k = ashiftr w x k.
Proof.
  intros w x k. apply N.bits_inj. intro i. rewrite !ashiftr_spec.
  destruct (N.ltb_spec i w); [|reflexivity]. cbn [andb].
  rewrite N.mod_pow2_bits_low by lia. reflexivity.
Qed.

(* The closed form the AArch64 code computes equals isinf_spec. *)
Lemma isinf_arm_bits: forall z,
  ((z >>> 62) mod 2^32)
  .& (((0 ⊖ (z mod 2^63 .^ INF64) .| z mod 2^63 .^ INF64) >>> 63) mod 2^32 .^ 4294967295)
  = isinf_spec z.
Proof.
  intro z. set (D := z mod 2^63 .^ INF64).
  assert (DB: D < 2^63) by (apply lxor_bound; [apply N.mod_lt; discriminate | reflexivity]).
  assert (V: N.testbit (msub 64 0 D .| D) 63 = negb (D =? 0)) by (apply neg_or_sign, DB).
  assert (DZ: (D =? 0) = (z mod 2^63 =? INF64)).
  { unfold D. destruct (N.eqb_spec (z mod 2^63) INF64) as [E|E].
    - rewrite E, N.lxor_nilpotent. reflexivity.
    - apply N.eqb_neq. intro H. apply E. apply N.lxor_eq, H. }
  unfold isinf_spec. rewrite <- DZ.
  apply N.bits_inj. intro i. rewrite N.land_spec.
  destruct (N.ltb_spec i 32) as [I|I].
  - (* low 32 bits *)
    rewrite N.mod_pow2_bits_low by exact I.
    rewrite N.lxor_spec, N.mod_pow2_bits_low by exact I.
    replace (N.testbit 4294967295 i) with true by
      (symmetry; change 4294967295 with (N.ones 32); apply N.ones_spec_low; exact I).
    rewrite !ashiftr_spec.
    replace (i <? 64) with true by (symmetry; apply N.ltb_lt; lia).
    replace (N.min (i + 63) (N.pred 64)) with 63 by lia. rewrite V.
    destruct (D =? 0) eqn:DE; cbn [negb xorb andb].
    + (* infinity: z mod 2^63 = INF64 *)
      assert (ZE: z mod 2^63 = INF64) by (apply N.eqb_eq; symmetry; exact DZ).
      destruct (N.eqb_spec i 0) as [->|I0].
      * replace (N.min (0 + 62) (N.pred 64)) with 62 by reflexivity.
        replace (N.testbit z 62) with true.
        { destruct (N.testbit z 63); reflexivity. }
        rewrite <- (N.mod_pow2_bits_low z 63 62) by lia. rewrite ZE. reflexivity.
      * replace (N.min (i + 62) (N.pred 64)) with 63 by lia.
        destruct (N.testbit z 63).
        -- symmetry. change (2^32 - 1) with (N.ones 32). apply N.ones_spec_low. exact I.
        -- symmetry. destruct i as [|p]. contradiction. destruct p; reflexivity.
    + (* not infinity *)
      rewrite Bool.andb_false_r. symmetry. apply N.bits_0.
  - (* bits >= 32 *)
    rewrite N.mod_pow2_bits_high by exact I. cbn [andb].
    destruct (D =? 0); [destruct (N.testbit z 63)|]; symmetry;
      try apply N.bits_0; apply N.bits_above_log2; cbn; lia.
Qed.

Definition isinf_exit (t:trace) := match t with (Addr 32,_)::_ => true | _ => false end.
Definition postcondition (z:N) (s:store) := s R_X0 = isinf_spec z.
Definition isinf_invs (z:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = z)
  | 32 => Some (postcondition z s)
  | _ => None
  end | _ => None end.

Theorem isinf_correct:
  forall s t s' x' z
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (Z: s R_Z0 = z),
  satisfies_all isinf_arm8 (isinf_invs z) isinf_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isinf_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into Z.
  repeat arm8_step.
  unfold postcondition. rewrite ashiftr_mod. apply isinf_arm_bits.
Qed.
