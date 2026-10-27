(* Scratch loop back edge and exit after the sum chunk has been copied. *)
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

Lemma wrapper_vc_scratch_tail : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_copy_return r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c5b1,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL STATE.
  destruct STATE as (k & K & KM & COMMON & ROUTE & IDX & DIFF & U & V & SUM & SCRATCH & UN & RESULT).
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  pose proof (proj1 (proj2 PRE)) as BN.
  pose proof (chunk_index_bounds (wrapper_n r) k BN K) as [IB BYTES].
  pose proof (proj1 COMMON) as SP.
  pose proof (proj1 (proj2 COMMON)) as LEN.
  set (out:=limb_ptr (wrapper_sum r) (k+170)).
  pose proof (wrapper_common_metadata r s 16 out PRE ltac:(lia) COMMON) as COMMON'.
  pose proof (wrapper_results_metadata r (s V_MEM64) 16 out _ _ _ _ PRE ltac:(lia) END END RESULT) as RESULT'.
  pose proof (wrapper_unread_metadata r (s V_MEM64) 16 out _ PRE ltac:(lia) END UN) as UN'.
  fold (chunk_end (wrapper_n r) k) in RESULT',UN'.
  assert (BSP:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)).
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  assert (CELL : forall offset, offset=0 \/ offset=8 \/ offset=24 ->
    ((s V_MEM64)[Ⓠwrapper_frame r+16:=out]) Ⓠ[wrapper_frame r+offset]=
    (s V_MEM64) Ⓠ[wrapper_frame r+offset]).
  { intros offset OFF. apply getmem_noverlap. apply bounded_cells_separate;
      unfold wrapper_frame; destruct OFF as [-> | [-> | ->]]; lia. }
  assert (CELL16 : ((s V_MEM64)[Ⓠwrapper_frame r+16:=out]) Ⓠ[wrapper_frame r+16]=out).
  { rewrite getmem_setmem by (vm_compute; easy). apply N.mod_small,mp2_mod_lt. }
  pose proof (cmp_gt_positive64 (wrapper_n r) (k+170) ltac:(lia) IB) as COMP.
  unfold cmp_gt64,cmp_of64 in COMP. psimpl in COMP.
  assert (PTR : (0x550+limb_ptr (wrapper_sum r) k) mod 2^64=out).
  { unfold out. rewrite N.add_comm. apply limb_ptr_next. }
  assert (MEM : (s V_MEM64)[Ⓠwrapper_frame r+16:=0x550+limb_ptr (wrapper_sum r) k]=
    (s V_MEM64)[Ⓠwrapper_frame r+16:=out]).
  { rewrite <-(setmem_mod_r 64 LittleE 8 (s V_MEM64) (wrapper_frame r+16)
      (0x550+limb_ptr (wrapper_sum r) k)). change (2^(8*8)) with (2^64). rewrite PTR. reflexivity. }
  pose proof (CELL 0 ltac:(tauto)) as CELL0. rewrite N.add_0_r in CELL0.
  do 5 x64_step.
  - rewrite msub_eqb_add64 in BC by lia. rewrite COMP in BC.
    replace (170+k) with (k+170) in BC by lia.
    assert (DONE:wrapper_n r<=k+170).
    { destruct (k+170 <? wrapper_n r) eqn:E; [discriminate BC | apply N.ltb_ge,E]. }
    pose proof (chunk_next_finish (wrapper_n r) k K DONE) as FIN.
    do 4 x64_step. split; [exact PRE | ].
    unfold wrapper_epilogue. nc_updates. psimpl.
    replace (16+wrapper_frame r) with (wrapper_frame r+16) by lia. rewrite MEM.
    unfold wrapper_common in COMMON'.
    repeat (rewrite update_updated in COMMON' || rewrite update_frame in COMMON' by discriminate).
    destruct COMMON' as (SP' & LEN' & SAVE' & FRAME').
    split; [reflexivity | ]. split; [exact SAVE' | ]. split; [exact FRAME' | ].
    apply wrapper_results_post with (cy:=(s V_MEM64) Ⓠ[wrapper_frame r])
      (borrow:=(s V_MEM64) Ⓠ[wrapper_frame r+8]).
    + rewrite FIN in RESULT'. exact RESULT'.
    + nc_updates. psimpl.
      replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia.
      rewrite N.mod_small; [lia | ]. destruct RESULT as (CY & BORROW & REST). lia.
  - rewrite msub_eqb_add64 in BC by lia. rewrite COMP in BC.
    replace (170+k) with (k+170) in BC by lia.
    assert (MORE:k+170<wrapper_n r).
    { destruct (k+170 <? wrapper_n r) eqn:E; [apply N.ltb_lt,E | discriminate BC]. }
    pose proof (proj2 (chunk_next_continue (wrapper_n r) k K MORE)) as FIN.
    split; [exact PRE | ]. unfold wrapper_loop.
    exists (k+170). split; [exact MORE | ]. split; [apply chunk_index_multiple,KM | ].
    unfold wrapper_common,wrapper_loop_regs. nc_updates. psimpl.
    replace (16+wrapper_frame r) with (wrapper_frame r+16) by lia. rewrite MEM.
    replace (24+wrapper_frame r) with (wrapper_frame r+24) by lia.
    replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia.
    replace (170+k) with (k+170) by lia.
    rewrite ?CELL16, ?(CELL 24 ltac:(tauto)), ?(CELL 8 ltac:(tauto)), ?CELL0.
    split.
    + unfold wrapper_common in COMMON'.
      repeat (rewrite update_updated in COMMON' || rewrite update_frame in COMMON' by discriminate).
      destruct COMMON' as (SP' & LEN' & SAVE' & FRAME').
      split; [reflexivity | ]. split; [reflexivity | ]. split; assumption.
    + split; [exact ROUTE | ]. split.
      * repeat split; try assumption; unfold out; try reflexivity; lia.
      * rewrite FIN in UN',RESULT'. replace (170+k) with (k+170) by lia. split; assumption.
Qed.
