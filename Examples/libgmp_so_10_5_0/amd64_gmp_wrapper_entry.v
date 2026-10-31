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

Ltac wrapper_entry_initialize r PRE POS STACK B BC BC0 :=
  split; [exact PRE | ];
  eapply (wrapper_loop_initialize AdditionFirst r _ (wrapper_prologue_memory r)); [
    exact PRE |
    exact POS |
    apply wrapper_route_add; [exact PRE | apply N.eqb_neq,BC | apply N.eqb_neq,BC0] |
    split; [apply wrapper_prologue_saved,PRE | ];
      split; [apply wrapper_prologue_memory_frame,PRE | apply wrapper_prologue_unread,PRE] |
    unfold wrapper_init_memory,wrapper_prologue_memory,wrapper_frame; nc_updates;
      repeat rewrite msub_sub by (clear -STACK; lia);
      repeat rewrite N.mod_small by (clear -B STACK; lia);
      replace (r R_RSP-0x5a0) with (r R_RSP-0x5a8+8) by lia; reflexivity |
    unfold wrapper_frame; nc_updates; rewrite msub_sub by lia;
      rewrite N.mod_small by lia; reflexivity |
    nc_updates; reflexivity |
    unfold wrapper_loop_regs,limb_ptr,wrapper_u,wrapper_v,wrapper_sum,wrapper_diff;
      nc_updates; rewrite N.lxor_nilpotent; psimpl; repeat split; reflexivity ].

Lemma wrapper_vc_entry_positive : forall r cc ac sc t,
  wrapper_pre r -> 0<wrapper_n r ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c360,r)::t).
Proof.
  intros r cc ac sc t PRE POS.
  pose proof (proj1 PRE) as MDL.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  assert (B:r R_RSP<2^64) by exact (models_var R_RSP MDL).
  assert (BN:r R_R8<2^63) by (unfold wrapper_pre,wrapper_n in *; lia).
  assert (NZ:(r R_R8 =? 0)=false) by (apply N.eqb_neq; unfold wrapper_n in POS; lia).
  do 14 x64_step.
  - abstract (split; [exact PRE | ]; split;
      [wrapper_prologue_projection PRE STACK B | left; apply N.eqb_eq in BC; exact BC]).
  - do 2 x64_step.
    + abstract (split; [exact PRE | ]; split;
        [wrapper_prologue_projection PRE STACK B | right; apply N.eqb_eq in BC0; exact BC0]).
    + x64_step. rewrite N.land_diag,(slt_nonnegative64 _ BN),NZ.
      x64_step; try discriminate. do 5 x64_step.
      abstract (wrapper_entry_initialize r PRE POS STACK B BC BC0).
Qed.
