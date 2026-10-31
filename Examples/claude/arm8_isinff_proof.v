(* isinff (AArch64 / ARMv8) -- test whether a float is infinite.

   SEMANTICS
   ---------
   isinff(x) returns 1 if x is +inf, -1 if x is -inf, and 0 otherwise.  The
   32-bit analogue of isinf: branch-free, with the +inf float pattern
   0x7f800000 and the sign/mask arithmetic shifts at 30 and 31.

     `fmov w0,s0; and w2,w0,#0x7fffffff; asr w0,w0,#0x1e;
      eor w2,w2,#0x7f800000; neg w1,w2; orr w1,w1,w2; asr w1,w1,#0x1f;
      bic w0,w0,w1; ret`

   SPECIFICATION (man 3 isinf)
   ---------------------------
     int isinf(float x);  /* via the type-generic isinf macro */

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
            symbol isinff at 0x13a1e0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Model:   Specification and proof written by Claude Opus 4.8 (claude-opus-4-8),
            an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   S0 (low 32 bits of Z0) holds the float's bits.
   Output:  W0 = 1 (+inf), 0xffffffff (-1) for -inf, else 0.  Memory is
            unchanged (leaf function, returns via X30).
 *)

Require Import Picinae_armv8.
Require Import isinff_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem isinff_nwc: forall s2 s1, isinff_arm8 s1 = isinff_arm8 s2.
Proof. reflexivity. Qed.
Theorem isinff_welltyped: welltyped_prog arm8typctx isinff_arm8.
Proof. Picinae_typecheck. Qed.
Theorem isinff_preserves_memory:
  forall_endstates isinff_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition INF32 := 2139095040.  (* 0x7f800000 *)

Definition isinff_spec (z:N) :=
  if z mod 2^31 =? INF32 then (if N.testbit z 31 then 2^32 - 1 else 1) else 0.

Lemma neg_or_sign32: forall D, D < 2^31 -> N.testbit (msub 32 0 D .| D) 31 = negb (D =? 0).
Proof.
  intros D DB. rewrite N.lor_spec. destruct (N.eqb_spec D 0) as [Z|Z].
  - subst D. reflexivity.
  - assert (E: msub 32 0 D = 2^32 - D).
    { rewrite msub_wrap by (rewrite N.mod_0_l, N.mod_small; lia).
      rewrite N.mod_0_l, N.mod_small by lia. lia. }
    rewrite E. replace (N.testbit D 31) with false.
    + rewrite Bool.orb_false_r. cbn [negb].
      change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
      rewrite N.testbit_eqb. rewrite N.eqb_eq.
      replace (4294967296 - D) with (2147483648 + (2147483648 - D)) by lia.
      rewrite <- (N.mul_1_l 2147483648) at 1. change 2147483648 with (2^31).
      rewrite N.div_add_l by discriminate. rewrite N.div_small by (change (2^31) with 2147483648; lia).
      reflexivity.
    + symmetry. apply N.bits_above_log2. apply N.log2_lt_pow2. lia. exact DB.
Qed.

Lemma ashiftr_mod: forall w x k, ashiftr w (x mod 2^w) k = ashiftr w x k.
Proof.
  intros w x k. apply N.bits_inj. intro i. rewrite !ashiftr_spec.
  destruct (N.ltb_spec i w); [|reflexivity]. cbn [andb].
  rewrite N.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma isinff_arm_bits: forall z,
  (ashiftr 32 z 30 mod 2^32)
  .& (ashiftr 32 (msub 32 0 (z mod 2^31 .^ INF32) .| z mod 2^31 .^ INF32) 31 mod 2^32 .^ 4294967295)
  = isinff_spec z.
Proof.
  intro z. set (D := z mod 2^31 .^ INF32).
  assert (DB: D < 2^31) by (apply lxor_bound; [apply N.mod_lt; discriminate | reflexivity]).
  assert (V: N.testbit (msub 32 0 D .| D) 31 = negb (D =? 0)) by (apply neg_or_sign32, DB).
  assert (DZ: (D =? 0) = (z mod 2^31 =? INF32)).
  { unfold D. destruct (N.eqb_spec (z mod 2^31) INF32) as [E|E].
    - rewrite E, N.lxor_nilpotent. reflexivity.
    - apply N.eqb_neq. intro H. apply E. apply N.lxor_eq, H. }
  unfold isinff_spec. rewrite <- DZ.
  apply N.bits_inj. intro i. rewrite N.land_spec.
  destruct (N.ltb_spec i 32) as [I|I].
  - (* low 32 bits *)
    rewrite N.mod_pow2_bits_low by exact I.
    rewrite N.lxor_spec, N.mod_pow2_bits_low by exact I.
    replace (N.testbit 4294967295 i) with true by
      (symmetry; change 4294967295 with (N.ones 32); apply N.ones_spec_low; exact I).
    rewrite !ashiftr_spec.
    replace (i <? 32) with true by (symmetry; apply N.ltb_lt; lia).
    replace (N.min (i + 31) (N.pred 32)) with 31 by lia. rewrite V.
    destruct (D =? 0) eqn:DE; cbn [negb xorb andb].
    + (* infinity: z mod 2^31 = INF32 *)
      assert (ZE: z mod 2^31 = INF32) by (apply N.eqb_eq; symmetry; exact DZ).
      destruct (N.eqb_spec i 0) as [->|I0].
      * replace (N.min (0 + 30) (N.pred 32)) with 30 by reflexivity.
        replace (N.testbit z 30) with true.
        { destruct (N.testbit z 31); reflexivity. }
        rewrite <- (N.mod_pow2_bits_low z 31 30) by lia. rewrite ZE. reflexivity.
      * replace (N.min (i + 30) (N.pred 32)) with 31 by lia.
        destruct (N.testbit z 31).
        -- symmetry. change (2^32 - 1) with (N.ones 32). apply N.ones_spec_low. exact I.
        -- symmetry. destruct i as [|p]. contradiction. destruct p; reflexivity.
    + (* not infinity *)
      rewrite Bool.andb_false_r. symmetry. apply N.bits_0.
  - (* bits >= 32 *)
    rewrite N.mod_pow2_bits_high by exact I. cbn [andb].
    destruct (D =? 0); [destruct (N.testbit z 31)|]; symmetry;
      try apply N.bits_0; apply N.bits_above_log2; cbn; lia.
Qed.

Definition isinff_exit (t:trace) := match t with (Addr 32,_)::_ => true | _ => false end.
Definition postcondition (z:N) (s:store) := s R_X0 = isinff_spec z.
Definition isinff_invs (z:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_Z0 = z)
  | 32 => Some (postcondition z s)
  | _ => None
  end | _ => None end.

Theorem isinff_correct:
  forall s t s' x' z
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (Z: s R_Z0 = z),
  satisfies_all isinff_arm8 (isinff_invs z) isinff_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isinff_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into Z.
  repeat arm8_step.
  unfold postcondition.
  rewrite !N.shiftr_0_r, !ashiftr_mod. apply isinff_arm_bits.
Qed.
