(* The addition-first loop's back edge and final return-value encoding. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_machine.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma wrapper_vc_add_tail : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_second_return AdditionFirst r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c420,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL STATE.
  destruct STATE as (k & K & KM & COMMON & ROUTE & UN & U & V & IDX & SUM & DIFF & RESULT).
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  pose proof (proj1 (proj2 PRE)) as BN.
  pose proof (chunk_index_bounds (wrapper_n r) k BN K) as [IB BYTES].
  pose proof (proj1 COMMON) as SP.
  pose proof (proj1 (proj2 COMMON)) as LEN.
  pose proof (wrapper_common_metadata r s 8 (s R_RAX) PRE ltac:(lia) COMMON) as COMMON'.
  pose proof (wrapper_results_metadata r (s V_MEM64) 8 (s R_RAX) _ _ _ _ PRE ltac:(lia) END END RESULT) as RESULT'.
  pose proof (wrapper_unread_metadata r (s V_MEM64) 8 (s R_RAX) _ PRE ltac:(lia) END UN) as UN'.
  fold (chunk_end (wrapper_n r) k) in RESULT',UN'.
  assert (BSP:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)).
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  assert (CELL : ((s V_MEM64)[Ⓠwrapper_frame r+8:=s R_RAX]) Ⓠ[wrapper_frame r]=
    (s V_MEM64) Ⓠ[wrapper_frame r]).
  { apply getmem_noverlap. apply bounded_cells_separate; unfold wrapper_frame; lia. }
  assert (CELL8 : ((s V_MEM64)[Ⓠwrapper_frame r+8:=s R_RAX]) Ⓠ[wrapper_frame r+8]=s R_RAX).
  { rewrite getmem_setmem by (vm_compute; easy). apply N.mod_small.
    pose proof (proj1 (proj2 RESULT)); lia. }
  pose proof (cmp_gt_positive64 (wrapper_n r) (k+170) ltac:(lia) IB) as COMP.
  unfold cmp_gt64,cmp_of64 in COMP. psimpl in COMP.
  do 3 x64_step.
  - rewrite msub_eqb_add64 in BC by lia. rewrite COMP in BC. replace (170+k) with (k+170) in BC by lia.
    assert (DONE:wrapper_n r<=k+170).
    { destruct (k+170 <? wrapper_n r) eqn:E; [discriminate BC | apply N.ltb_ge,E]. }
    pose proof (chunk_next_finish (wrapper_n r) k K DONE) as FIN.
    do 2 x64_step. split; [exact PRE | ].
    unfold wrapper_epilogue. nc_updates. psimpl.
    replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia.
    rewrite ?CELL. unfold wrapper_common in COMMON'.
    repeat (rewrite update_updated in COMMON' || rewrite update_frame in COMMON' by discriminate).
    destruct COMMON' as (SP' & LEN' & SAVE' & FRAME').
    split; [reflexivity | ]. split; [exact SAVE' | ]. split; [exact FRAME' | ].
    apply wrapper_results_post with (cy:=(s V_MEM64) Ⓠ[wrapper_frame r]) (borrow:=s R_RAX).
    + rewrite FIN in RESULT'. exact RESULT'.
    + nc_updates. rewrite N.mod_small; [lia | ].
      destruct RESULT as (CY & BORROW & REST). lia.
  - rewrite msub_eqb_add64 in BC by lia. rewrite COMP in BC. replace (170+k) with (k+170) in BC by lia.
    assert (MORE:k+170<wrapper_n r).
    { destruct (k+170 <? wrapper_n r) eqn:E; [apply N.ltb_lt,E | discriminate BC]. }
    pose proof (proj2 (chunk_next_continue (wrapper_n r) k K MORE)) as FIN.
    split; [exact PRE | ]. unfold wrapper_loop.
    exists (k+170). split; [exact MORE | ].
    split; [apply chunk_index_multiple,KM | ].
    unfold wrapper_common,wrapper_loop_regs. nc_updates. psimpl.
    replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia.
    rewrite ?CELL,?CELL8.
    split.
    + unfold wrapper_common in COMMON'.
      repeat (rewrite update_updated in COMMON' || rewrite update_frame in COMMON' by discriminate).
      destruct COMMON' as (SP' & LEN' & SAVE' & FRAME').
      split; [reflexivity | ]. split; [reflexivity | ]. split; assumption.
    + split; [exact ROUTE | ]. split; [repeat split; try assumption; lia | ].
      rewrite FIN in UN',RESULT'. replace (170+k) with (k+170) by lia. split; assumption.
Qed.
