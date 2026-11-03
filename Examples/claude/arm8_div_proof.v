(* div -- signed 32-bit quotient and remainder, AArch64 / ARMv8.

   C specification: div_t div(int numerator, int denominator) returns quot
   rounded toward zero and rem, with quot * denominator + rem = numerator.
   Provenance (inherited, not independently validated by this proof unit):
   /lib/aarch64-linux-gnu/libc.so.6, Ubuntu glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06;
   symbol div at 0x13d840 (Ghidra image base 0x100000), rebased entry 0.
   Lifter: Ghidra 11.4.2 + pcode2coq. Generated div_arm8.v is unchanged.
   Author/model: OpenAI GPT-6 Astra, porting the arithmetic specification
   of Claude Opus 5.5's amd64_div_proof.v without AMD64 program logic.

   AAPCS64 input: signed low 32 bits of X0/X1 (W0/W1) are n/d; upper bits
   are unrestricted within the 64-bit register model. Exclude only d = 0
   and (n = INT_MIN, d = -1). No pointer, size, overlap, CPU-feature or
   tunable hypotheses. Output at RET offset 24: signed X0[31:0] = Z.quot
   n d, signed X0[63:32] = Z.rem n d. The lift uses SDIV, MSUB, BFXIL,
   then BFM to construct this packing. Memory, SP, X19-X29 and X30 are
   preserved, as are the full modeled SIMD registers Z8-Z15.
   The theorem is partial correctness of this IL, not a termination or
   independently established binary/lifter-soundness theorem.
*)
Require Import Picinae_armv8 div_arm8 arm8_common div_arith.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem div_nwc: forall s2 s1, div_arm8 s1 = div_arm8 s2.
Proof. reflexivity. Qed.
Theorem div_welltyped: welltyped_prog arm8typctx div_arm8.
Proof. exact div_arm8.welltyped. Qed.
Theorem div_preserves_memory:
  forall_endstates div_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Theorem div_preserves_callee_saved:
  forall v, In v [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
                  R_X26; R_X27; R_X28; R_X29; R_X30; R_SP;
                  R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15] ->
  forall_endstates div_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The BFXIL/BFM result really places the remainder in X0[63:32]. *)
Lemma div_packed_hi: forall q r,
  (q mod 2^32 .| (r << 32 .& 18446744069414584320)) >> 32 = r mod 2^32.
Proof.
  intros. rewrite N.shiftr_lor.
  change 18446744069414584320 with (N.ones 32 << 32).
  rewrite shr_land_shl, N.shiftr_shiftl_l by reflexivity.
  rewrite N.sub_diag, N.shiftl_0_r.
  rewrite N.shiftr_div_pow2, N.div_small by apply mp2_mod_lt.
  apply N.lor_0_l.
Qed.

Definition div_exit (t:trace) :=
  match t with (Addr 24,_)::_ => true | _ => false end.
Definition postcondition (n d:Z) (s:store) :=
  toZ 32 (s R_X0 mod 2^32) = Z.quot n d /\
  toZ 32 (s R_X0 >> 32) = Z.rem n d /\
  Z.add (Z.mul (toZ 32 (s R_X0 mod 2^32)) d) (toZ 32 (s R_X0 >> 32)) = n.
Definition div_invs (n d:Z) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_X0) = n /\ toZ 32 (s R_X1) = d)
  | 24 => Some (postcondition n d s)
  | _ => None
  end | _ => None end.

Theorem div_correct:
  forall s t s' x' n d
    (ENTRY: startof t (x',s') = (Addr 0,s))
    (MDL: models arm8typctx s)
    (HN: toZ 32 (s R_X0) = n) (HD: toZ 32 (s R_X1) = d)
    (DNZ: d <> 0%Z) (NOVF: ~ (n = (-2^31)%Z /\ d = (-1)%Z)),
  satisfies_all div_arm8 (div_invs n d) div_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply div_welltyped. intro MDL1.
  clear - PRE MDL1 DNZ NOVF. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [HN HD].
  repeat arm8_step.
  - clear - HD DNZ BC.
    destruct (N.eqb_spec (s1 R_X1 mod 2^32) 0) as [DZ|DZ].
    + exfalso. apply DNZ. rewrite <- HD, <- (toZ_mod_pow2 32 32) by reflexivity.
      rewrite DZ. apply toZ_0_r.
    + simpl in BC. discriminate.
  - rewrite !N.shiftr_0_r, !mp2_mod_mod.
    unfold sbop2. rewrite !toZ_mod_pow2, HN, HD by reflexivity.
    rewrite div_packed_hi.
    assert (RN: (-2^31 <= n < 2^31)%Z).
      rewrite <- HN. apply (canonicalZ_bounds 32).
    assert (RD: (-2^31 <= d < 2^31)%Z).
      rewrite <- HD. apply (canonicalZ_bounds 32).
    assert (QR: signed_range 32 (Z.quot n d)).
      clear - RN RD DNZ NOVF. unfold signed_range.
      apply (quot_range n d (2^31)); lia.
    assert (RR: signed_range 32 (Z.rem n d)).
      clear - RD DNZ. unfold signed_range.
      apply (rem_range n d (2^31)); lia.
    assert (REM: msub 32 (s1 R_X0) (ofZ 32 (Z.quot n d) * s1 R_X1) =
                 ofZ 32 (Z.rem n d)).
    { rewrite msub_sbop, toZ_mul, canonicalZ_sub_r, toZ_ofZ_canonicalZ by reflexivity.
      rewrite (canonicalZ_id 32) by (reflexivity || exact QR).
      rewrite HN, HD. f_equal.
      clear - DNZ. pose proof (Z.quot_rem n d DNZ). nia. }
    rewrite REM, !toZ_mod_pow2, !toZ_ofZ_canonicalZ by reflexivity.
    rewrite !(canonicalZ_id 32) by (reflexivity || assumption).
    repeat split. clear - DNZ. pose proof (Z.quot_rem n d DNZ). nia.
Qed.

(* Every pair of signed C ints has a typed entry store; hence the functional
   theorem's input hypotheses do not constrain the result or hide a contract. *)
Theorem div_inputs_satisfiable: forall n d,
  signed_range 32 n -> signed_range 32 d ->
  exists s, models arm8typctx s /\
            toZ 32 (s R_X0) = n /\ toZ 32 (s R_X1) = d.
Proof.
  intros n d RN RD.
  exists (update (update (fun _ => 0) R_X0 (ofZ 32 n)) R_X1 (ofZ 32 d)).
  split.
  - apply models_update.
    + cbn. eapply N.lt_le_trans; [apply ofZ_bound|].
      change (2^32 <= 2^64). apply N.pow_le_mono_r; discriminate.
    + apply models_update.
      * cbn. eapply N.lt_le_trans; [apply ofZ_bound|].
        change (2^32 <= 2^64). apply N.pow_le_mono_r; discriminate.
      * intros v w CV. apply N.neq_0_lt_0. intro H.
        apply (pow2_nonzero w). exact H.
  - change (toZ 32 (ofZ 32 n) = n /\ toZ 32 (ofZ 32 d) = d).
    rewrite !toZ_ofZ_canonicalZ by reflexivity.
    rewrite !(canonicalZ_id 32) by (reflexivity || assumption).
    split; reflexivity.
Qed.
