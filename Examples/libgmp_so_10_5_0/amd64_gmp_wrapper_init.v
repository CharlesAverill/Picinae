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

Definition wrapper_memory_ok r m :=
  wrapper_saved r m /\ wrapper_memory_frame r m /\ wrapper_unread r m 0.
Definition wrapper_init_memory route r m :=
  match route with
  | AdditionFirst => m[Ⓠwrapper_frame r+8:=0][Ⓠwrapper_frame r:=0]
  | SubtractionFirst => m[Ⓠwrapper_frame r:=0][Ⓠwrapper_frame r+8:=0]
  | Scratch => m[Ⓠwrapper_frame r+16:=wrapper_sum r][Ⓠwrapper_frame r+8:=0]
      [Ⓠwrapper_frame r:=0][Ⓠwrapper_frame r+24:=wrapper_frame r+32]
  end.
Lemma wrapper_memory_ok_metadata : forall r m offset out,
  wrapper_pre r -> offset+8<=0x578 -> wrapper_memory_ok r m ->
  wrapper_memory_ok r (m[Ⓠwrapper_frame r+offset:=out]).
Proof.
  intros r m offset out PRE OFF (SAVED & FRAME & UN).
  set (s:=r[R_RSP:=wrapper_frame r][R_R12:=wrapper_n r][V_MEM64:=m]).
  assert (COMMON:wrapper_common r s).
  { unfold wrapper_common,s. nc_updates. repeat (split; [reflexivity | ]).
    split; assumption. }
  pose proof (wrapper_common_metadata r s offset out PRE OFF COMMON) as NEW.
  unfold wrapper_common,s in NEW. nc_updates.
  repeat (rewrite update_updated in NEW || rewrite update_frame in NEW by discriminate).
  destruct NEW as (_ & _ & SAVE' & FRAME').
  split; [exact SAVE' | ]. split; [exact FRAME' | ].
  eapply wrapper_unread_metadata; eassumption || lia.
Qed.
Lemma wrapper_memory_ok_metadata0 : forall r m out,
  wrapper_pre r -> wrapper_memory_ok r m -> wrapper_memory_ok r (m[Ⓠwrapper_frame r:=out]).
Proof. intros. pose proof (wrapper_memory_ok_metadata r m 0 out H ltac:(lia) H0) as P.
  rewrite N.add_0_r in P. exact P. Qed.
Lemma wrapper_memory_ok_init : forall route r m,
  wrapper_pre r -> wrapper_memory_ok r m -> wrapper_memory_ok r (wrapper_init_memory route r m).
Proof.
  intros [] r m PRE OK; unfold wrapper_init_memory;
    repeat first [apply wrapper_memory_ok_metadata0; [exact PRE | ] |
      apply wrapper_memory_ok_metadata; [exact PRE | lia | ]]; exact OK.
Qed.
Lemma wrapper_init_cells : forall route r m,
  wrapper_pre r ->
  let m':=wrapper_init_memory route r m in
  m' Ⓠ[wrapper_frame r]=0 /\ m' Ⓠ[wrapper_frame r+8]=0 /\
  (route=Scratch -> m' Ⓠ[wrapper_frame r+16]=wrapper_sum r /\
     m' Ⓠ[wrapper_frame r+24]=wrapper_frame r+32).
Proof.
  intros route r m PRE. cbv zeta.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  assert (BSP:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)).
  assert (BSUM:wrapper_sum r<2^64) by exact (models_var R_RDI (proj1 PRE)).
  destruct route; unfold wrapper_init_memory;
    repeat split; intros; try discriminate;
    repeat first [rewrite getmem_setmem by (vm_compute; easy) |
      rewrite getmem_noverlap by (apply bounded_cells_separate; unfold wrapper_frame; lia)];
    try reflexivity; apply N.mod_small; unfold wrapper_frame; lia.
Qed.

Lemma wrapper_loop_initialize : forall route r s m,
  wrapper_pre r -> 0<wrapper_n r -> wrapper_route_ok route r -> wrapper_memory_ok r m ->
  s V_MEM64=wrapper_init_memory route r m -> s R_RSP=wrapper_frame r -> s R_R12=wrapper_n r ->
  wrapper_loop_regs route r s 0 -> wrapper_loop route r s.
Proof.
  intros route r s m PRE POS ROUTE OK MEM SP LEN REGS.
  pose proof (wrapper_memory_ok_init route r m PRE OK) as (SAVED & FRAME & UN).
  pose proof (wrapper_init_cells route r m PRE) as (C0 & C8 & SCRATCH).
  unfold wrapper_loop. exists 0. split; [exact POS | ]. split; [reflexivity | ].
  split; [unfold wrapper_common; rewrite MEM; repeat (split; [assumption | ]); assumption | ].
  split; [exact ROUTE | ]. split; [exact REGS | ].
  rewrite MEM. split; [exact UN | ].
  destruct route; rewrite ?N.add_0_r,C0,C8; apply wrapper_results_zero.
Qed.

Lemma wrapper_route_add : forall r,
  wrapper_pre r -> wrapper_sum r<>wrapper_u r -> wrapper_sum r<>wrapper_v r ->
  wrapper_route_ok AdditionFirst r.
Proof.
  intros r (MDL & BN & B & STACK & DISJ & ALIAS & SEP) U V.
  unfold wrapper_route_ok. split.
  - destruct (ALIAS (wrapper_sum r) ltac:(tauto) (wrapper_u r) ltac:(tauto)); tauto.
  - destruct (ALIAS (wrapper_sum r) ltac:(tauto) (wrapper_v r) ltac:(tauto)); tauto.
Qed.
Lemma wrapper_route_sub : forall r,
  wrapper_pre r -> (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r) ->
  wrapper_diff r<>wrapper_u r -> wrapper_diff r<>wrapper_v r ->
  wrapper_route_ok SubtractionFirst r.
Proof.
  intros r (MDL & BN & B & STACK & DISJ & ALIAS & SEP) SUM U V.
  split; [exact SUM | ]. split.
  - destruct (ALIAS (wrapper_diff r) ltac:(tauto) (wrapper_u r) ltac:(tauto)); tauto.
  - destruct (ALIAS (wrapper_diff r) ltac:(tauto) (wrapper_v r) ltac:(tauto)); tauto.
Qed.
Lemma slt_nonnegative64 : forall x, x<2^63 -> slt 64 x 0=false.
Proof. intros x B. unfold slt. rewrite toZ_0_r,toZ_nonnegative64 by assumption.
  apply Z.ltb_ge; lia. Qed.

