(* Addition-first loop header through its concrete arithmetic CALL site. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_machine.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_header_specs.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Ltac wrapper_add_header_finish r s k PRE MDL ORIGIN CONT K IDX DIFF Q :=
  do 3 x64_step;
  eapply models_after_steps; [exact MDL | apply gmp_linked_welltyped | ];
  let CURRENT:=fresh "CURRENT" in intro CURRENT;
  match goal with |- nextinv _ _ _ _ ((Addr _,?after)::_) =>
    let DATA:=fresh "DATA" in
    assert (DATA:wrapper_header_data AdditionFirst r s after k) by
      (abstract (unfold wrapper_header_data,wrapper_header_memory; nc_updates; rewrite Q; psimpl;
        replace (16+wrapper_frame r) with (wrapper_frame r+16) by lia;
        repeat first [reflexivity | assumption | solve [lia] |
          match goal with |- _ /\ _ => split end |
          solve [rewrite N.add_comm; apply limb_ptr_next] ]));
    eapply CONT; [exact K | exact CURRENT | exact DATA |
      eapply (wrapper_header_ready AdditionFirst r s after k); eassumption]
  end.

Lemma wrapper_vc_add_header : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_loop AdditionFirst r s ->
  (forall k after tr, k<wrapper_n r -> models x64typctx after ->
    wrapper_header_data AdditionFirst r s after k -> wrapper_nc_call_ready after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c3ea,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c3b8,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL LOOP CONT. pose proof LOOP as ORIGIN.
  destruct LOOP as (k & K & KM & COMMON & ROUTE & REGS & UN & RESULT).
  destruct REGS as (U & V & IDX & SUM & DIFF).
  pose proof (proj1 COMMON) as SP. pose proof (proj1 (proj2 COMMON)) as LEN.
  pose proof (proj1 (proj2 PRE)) as BN.
  assert (REM:wrapper_n r ⊖ k=wrapper_n r-k).
  { rewrite msub_sub by lia. apply N.mod_small; lia. }
  pose proof (cmp_gt_raw_positive64 (wrapper_n r-k) 170 ltac:(lia) ltac:(lia)) as COMP.
  unfold cmp_of_raw64 in COMP. psimpl in COMP.
  do 4 x64_step. rewrite REM.
  do 4 x64_step. x64_step.
  - rewrite COMP in BC.
    assert (Q:chunk_size (wrapper_n r) k=170).
    { unfold chunk_size. destruct (170 <? wrapper_n r-k) eqn:E; [apply N.min_l; apply N.ltb_lt in E; lia | discriminate BC]. }
    wrapper_add_header_finish r s k PRE MDL ORIGIN CONT K IDX DIFF Q.
  - rewrite COMP in BC.
    assert (Q:chunk_size (wrapper_n r) k=wrapper_n r-k).
    { unfold chunk_size. destruct (170 <? wrapper_n r-k) eqn:E; [discriminate BC | apply N.min_r; apply N.ltb_ge,E]. }
    wrapper_add_header_finish r s k PRE MDL ORIGIN CONT K IDX DIFF Q.
Qed.
