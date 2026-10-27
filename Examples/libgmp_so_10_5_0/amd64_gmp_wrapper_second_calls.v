(* Argument setup at the three first-callee return points. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_next_call_specs.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Ltac wrapper_second_setup route r s k PRE MDL ORIGIN CONT K :=
  do 9 x64_step;
  eapply models_after_steps; [exact MDL | apply gmp_linked_welltyped | ];
  let CURRENT:=fresh "CURRENT" in intro CURRENT;
  match goal with |- nextinv _ _ _ _ ((Addr _,?after)::_) =>
    let DATA:=fresh "DATA" in
    assert (DATA:wrapper_second_call_data route r s after k) by
      (abstract (unfold wrapper_second_call_data; nc_updates; psimpl;
        replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia;
        repeat first [reflexivity | assumption | solve [lia] |
          match goal with |- _ /\ _ => split end |
          solve [rewrite N.add_comm; apply limb_ptr_next] ]));
    eapply CONT; [exact K | exact CURRENT | exact DATA |
      eapply (wrapper_second_call_ready route r s after k); eassumption]
  end.

Lemma wrapper_vc_add_second_call : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_first_return AdditionFirst r s ->
  (forall k after tr, k<wrapper_n r -> models x64typctx after ->
    wrapper_second_call_data AdditionFirst r s after k -> wrapper_nc_call_ready after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c41b,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c3ef,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL FIRST CONT. pose proof FIRST as ORIGIN.
  destruct FIRST as (k & K & KM & COMMON & ROUTE & UN & U & V & IDX & SUM & DIFF & CHUNK & RESULT).
  pose proof (proj1 COMMON) as SP. pose proof (proj1 (proj2 COMMON)) as LEN.
  assert (CNT:(s V_MEM64) Ⓠ[16+wrapper_frame r]=chunk_size (wrapper_n r) k)
    by (rewrite N.add_comm; exact CHUNK).
  wrapper_second_setup AdditionFirst r s k PRE MDL ORIGIN CONT K.
Qed.

Lemma wrapper_vc_sub_second_call : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_first_return SubtractionFirst r s ->
  (forall k after tr, k<wrapper_n r -> models x64typctx after ->
    wrapper_second_call_data SubtractionFirst r s after k -> wrapper_nc_call_ready after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c4e3,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c4b7,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL FIRST CONT. pose proof FIRST as ORIGIN.
  destruct FIRST as (k & K & KM & COMMON & ROUTE & UN & U & V & IDX & DIFF & SUM & CHUNK & RESULT).
  pose proof (proj1 COMMON) as SP. pose proof (proj1 (proj2 COMMON)) as LEN.
  assert (CNT:(s V_MEM64) Ⓠ[16+wrapper_frame r]=chunk_size (wrapper_n r) k)
    by (rewrite N.add_comm; exact CHUNK).
  wrapper_second_setup SubtractionFirst r s k PRE MDL ORIGIN CONT K.
Qed.

Lemma wrapper_vc_scratch_second_call : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_first_return Scratch r s ->
  (forall k after tr, k<wrapper_n r -> models x64typctx after ->
    wrapper_second_call_data Scratch r s after k -> wrapper_nc_call_ready after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c592,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c568,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL FIRST CONT. pose proof FIRST as ORIGIN.
  destruct FIRST as (k & K & KM & COMMON & ROUTE & UN & U & V & IDX & DIFF & COUNT & REST).
  pose proof (proj1 COMMON) as SP. pose proof (proj1 (proj2 COMMON)) as LEN.
  wrapper_second_setup Scratch r s k PRE MDL ORIGIN CONT K.
Qed.
