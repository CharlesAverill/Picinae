(* Positive-length entry and alias dispatch into the three chunk loops. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_machine.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_control.
From Stdlib Require Import NArith ZArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_init.

Lemma wrapper_vc_scratch_positive : forall r cc ac sc s t,
  wrapper_pre r -> 0<wrapper_n r -> models x64typctx s ->
  wrapper_dispatch r s -> wrapper_route_ok Scratch r ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c508,s)::t).
Proof.
  intros r cc ac sc s t PRE POS MDL [COMMON [UN [SUM [DIFF [U V]]]]] ROUTE.
  pose proof (proj1 COMMON) as SP.
  pose proof (proj1 (proj2 COMMON)) as LEN.
  assert (BN:wrapper_n r<2^63) by (unfold wrapper_pre in PRE; lia).
  assert (NZ:(wrapper_n r =? 0)=false) by (apply N.eqb_neq; lia).
  x64_step. rewrite ?LEN,N.land_diag,(slt_nonnegative64 _ BN),NZ.
  x64_step; try discriminate. do 7 x64_step.
  split; [exact PRE | ].
  eapply (wrapper_loop_initialize Scratch r _ (s V_MEM64)).
  - exact PRE.
  - exact POS.
  - exact ROUTE.
  - unfold wrapper_memory_ok,wrapper_common in *; tauto.
  - unfold wrapper_init_memory. nc_updates. psimpl.
    rewrite ?SUM. repeat rewrite (N.add_comm (wrapper_frame r)). reflexivity.
  - nc_updates. first [reflexivity | exact SP].
  - nc_updates. first [reflexivity | exact LEN].
  - pose proof (wrapper_init_cells Scratch r (s V_MEM64) PRE) as (C0 & C8 & CS).
    destruct (CS eq_refl) as [CSUM CSP].
    unfold wrapper_loop_regs. nc_updates. rewrite N.lxor_nilpotent. psimpl.
    rewrite ?SUM. replace (16+wrapper_frame r) with (wrapper_frame r+16) by lia.
    replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia.
    replace (24+wrapper_frame r) with (wrapper_frame r+24) by lia.
    replace (32+wrapper_frame r) with (wrapper_frame r+32) by lia.
    split; [rewrite ?U; unfold limb_ptr; psimpl; reflexivity | ].
    split; [rewrite ?V; unfold limb_ptr; psimpl; reflexivity | ].
    split; [reflexivity | ]. split; [rewrite ?DIFF; unfold limb_ptr; psimpl; reflexivity | ].
    unfold wrapper_init_memory in CSUM,CSP. rewrite ?CSUM,?CSP.
    unfold limb_ptr. psimpl. split; [reflexivity | ].
    apply N.mod_small.
    assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
    assert (BSP:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)).
    unfold wrapper_frame. lia.
Qed.

Lemma wrapper_vc_alias_positive : forall r cc ac sc s t,
  wrapper_pre r -> 0<wrapper_n r -> models x64typctx s ->
  wrapper_dispatch r s -> (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c448,s)::t).
Proof.
  intros r cc ac sc s t PRE POS MDL DISPATCH ALIAS.
  destruct DISPATCH as [COMMON [UN [SUM [DIFF [U V]]]]].
  pose proof (proj1 (proj2 COMMON)) as LEN.
  pose proof (proj1 COMMON) as SP.
  assert (BN:wrapper_n r<2^63) by (unfold wrapper_pre in PRE; lia).
  assert (NZ:(wrapper_n r =? 0)=false) by (apply N.eqb_neq; lia).
  do 2 x64_step.
  - abstract (split; [exact PRE | ]; split;
      [unfold wrapper_dispatch,wrapper_common; nc_updates; unfold wrapper_common in COMMON; tauto |
       unfold wrapper_route_ok; split; [exact ALIAS | left; apply N.eqb_eq in BC; congruence]]).
  - do 2 x64_step.
    + abstract (split; [exact PRE | ]; split;
        [unfold wrapper_dispatch,wrapper_common; nc_updates; unfold wrapper_common in COMMON; tauto |
         unfold wrapper_route_ok; split; [exact ALIAS | right; apply N.eqb_eq in BC0; congruence]]).
    + x64_step. rewrite ?LEN,N.land_diag,(slt_nonnegative64 _ BN),NZ.
      x64_step; try discriminate. do 5 x64_step.
      split; [exact PRE | ].
      eapply (wrapper_loop_initialize SubtractionFirst r _ (s V_MEM64)).
      * exact PRE.
      * exact POS.
      * apply wrapper_route_sub; [exact PRE | exact ALIAS | | ];
          apply N.eqb_neq in BC,BC0; congruence.
      * unfold wrapper_memory_ok,wrapper_common in *; tauto.
      * unfold wrapper_init_memory. nc_updates. psimpl.
        repeat rewrite (N.add_comm (wrapper_frame r)). reflexivity.
      * nc_updates. first [reflexivity | exact SP].
      * nc_updates. first [reflexivity | exact LEN].
      * unfold wrapper_loop_regs,limb_ptr. nc_updates. rewrite N.lxor_nilpotent. psimpl.
        rewrite ?U,?V,?SUM,?DIFF. unfold wrapper_u,wrapper_v,wrapper_sum,wrapper_diff.
        psimpl. repeat split; reflexivity.
Qed.
