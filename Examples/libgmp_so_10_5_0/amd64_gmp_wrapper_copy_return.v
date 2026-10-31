(* Copying the scratch sum commits the last buffered result of a chunk. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_copy_setup.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_return_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma copy_resume_frame : forall r caller ra after,
  wrapper_pre r -> models x64typctx caller -> caller R_RSP=wrapper_frame r ->
  copy_resume_post (copy_after_call caller ra) after ->
  leaf_abi caller after /\ wrapper_call_frame r (caller V_MEM64) (after V_MEM64)
    (caller R_RDI) (8*caller R_RDX).
Proof.
  intros r caller ra after PRE MDL SP POST.
  pose proof (copy_resume_caller_frame caller ra after MDL POST) as [ABI OUT].
  split; [exact ABI | ]. intros p len DST CELL. rewrite OUT by exact DST.
  unfold call_enter. nc_updates. rewrite SP,wrapper_call_cell by exact PRE.
  apply getmem_noverlap,CELL.
Qed.
Lemma wrapper_copy_return_certificate : forall r before caller ra after k,
  wrapper_pre r -> models x64typctx caller -> k<wrapper_n r ->
  wrapper_second_return Scratch r before -> wrapper_copy_call_data r before caller k ->
  copy_resume_post (copy_after_call caller ra) after -> wrapper_copy_return r after.
Proof.
  intros r before caller ra after k PRE MDL K SECOND DATA POST.
  pose proof DATA as PACKET.
  destruct DATA as (OLDCOUNT & OLDIDX & MEM & SP & LEN & DI & SI & DX & IDX & DIFF & U & V & SUM).
  destruct SECOND as (j & J & JM & COMMON & ROUTE & UN & U0 & V0 & INDEX & D0 & COUNT & SUMCELL & SCRATCHCELL & BORROW & BUFFER).
  assert (JK:j=k) by lia. rewrite JK in *.
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  fold (chunk_end (wrapper_n r) k) in END.
  pose proof (wrapper_common_metadata r before 8 (before R_RAX) PRE ltac:(lia) COMMON) as CBASE.
  assert (CC:wrapper_common r caller).
  { unfold wrapper_common in CBASE |- *. nc_updates.
    repeat (rewrite update_updated in CBASE || rewrite update_frame in CBASE by discriminate).
    rewrite MEM. split; [exact SP | ]. split; [exact LEN | ]. tauto. }
  pose proof (copy_resume_frame r caller ra after PRE MDL SP POST) as [ABI FRAME].
  rewrite DI,DX in FRAME.
  pose proof (wrapper_common_result r caller after (wrapper_sum r) k
    (chunk_size (wrapper_n r) k) PRE END ltac:(tauto) CC ABI FRAME) as COMMON'.
  assert (COPY:value (after V_MEM64) (wrapper_sum r+8*k) (chunk_size (wrapper_n r) k)=
    value (before V_MEM64) (wrapper_frame r+32) (chunk_size (wrapper_n r) k)).
  { pose proof (wrapper_copy_ready r before caller k PRE K PACKET) as (B & SAFE & SEP & CELL).
    pose proof (copy_resume_original_input caller ra after B CELL POST) as EQ.
    change (value (after V_MEM64) (caller R_RDI) (caller R_RDX)=value (caller V_MEM64) (caller R_RSI) (caller R_RDX)) in EQ.
    rewrite DI,SI,DX,value_limb_ptr,MEM in EQ. rewrite EQ.
    apply getmem_noverlap. apply noverlap_symmetry.
    eapply wrapper_scratch_stack_read; [exact PRE | exact QB | lia | left; lia]. }
  assert (LOW:value (after V_MEM64) (wrapper_sum r) k=value (before V_MEM64) (wrapper_sum r) k).
  { transitivity (value (caller V_MEM64) (wrapper_sum r) k).
    - apply FRAME.
      + unfold limb_ptr. apply noverlap_symmetry. rewrite noverlap_mod_idemp_l. apply noverlap_symmetry.
        apply noverlap_adjacent64. pose proof (proj1 (proj2 (proj2 PRE))) as B. unfold chunk_end in END. unfold GMPArrayParams.bytes. nia.
      + pose proof (wrapper_operand_call_cell r (wrapper_sum r) 0 k PRE ltac:(tauto) ltac:(lia)) as H.
        unfold limb_ptr in H. rewrite N.mul_0_r,N.add_0_r,noverlap_mod_idemp_l,wrapper_call_cell in H by exact PRE. exact H.
    - rewrite MEM. apply wrapper_metadata_array; eassumption || lia || tauto. }
  pose proof (wrapper_scratch_commit r (before V_MEM64) (after V_MEM64) k
    (chunk_size (wrapper_n r) k) ((before V_MEM64) Ⓠ[wrapper_frame r]) BUFFER LOW COPY) as [CY SUMEQ].
  fold (chunk_end (wrapper_n r) k) in SUMEQ.
  assert (DIFFVALUE:value (after V_MEM64) (wrapper_diff r) (chunk_end (wrapper_n r) k)=
    value (before V_MEM64) (wrapper_diff r) (chunk_end (wrapper_n r) k)).
  { rewrite (wrapper_frame_prefix_value r (caller V_MEM64) (after V_MEM64) (wrapper_sum r) k
      (chunk_size (wrapper_n r) k) (wrapper_diff r) (chunk_end (wrapper_n r) k) PRE END END ltac:(tauto)
      (noverlap_symmetry _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 PRE)))))) FRAME),MEM.
    apply wrapper_metadata_array; eassumption || lia || tauto. }
  assert (META8:(after V_MEM64) Ⓠ[wrapper_frame r+8]=before R_RAX).
  { rewrite (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (wrapper_sum r) k
      (chunk_size (wrapper_n r) k) 8 PRE END ltac:(lia) ltac:(tauto) FRAME),MEM,getmem_setmem by (vm_compute; easy).
    apply N.mod_small. pose proof (proj1 BORROW). lia. }
  assert (META:forall offset, offset=0 \/ offset=24 ->
    (after V_MEM64) Ⓠ[wrapper_frame r+offset]=(before V_MEM64) Ⓠ[wrapper_frame r+offset]).
  { intros offset OFF. rewrite (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (wrapper_sum r) k
      (chunk_size (wrapper_n r) k) offset PRE END ltac:(destruct OFF; lia) ltac:(tauto) FRAME),MEM.
    apply getmem_noverlap. apply bounded_cells_separate;
      assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto);
      assert (B:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)); unfold wrapper_frame;
      destruct OFF as [-> | ->]; lia. }
  pose proof (META 0 ltac:(tauto)) as META0. rewrite N.add_0_r in META0.
  assert (UN':wrapper_unread r (after V_MEM64) (chunk_end (wrapper_n r) k)).
  { assert (UC:wrapper_unread r (caller V_MEM64) (chunk_end (wrapper_n r) k)).
    { rewrite MEM. eapply wrapper_unread_metadata; [exact PRE | lia | exact END | exact UN]. }
    pose proof PRE as ROOT. destruct PRE as (MD & BN & B & ST & DS & ALIAS & SEP).
    assert (SU:forward_safe (wrapper_sum r) (wrapper_u r) (wrapper_n r))
      by (apply wrapper_alias_forward_safe; [apply ALIAS; tauto | exact B]).
    assert (SV:forward_safe (wrapper_sum r) (wrapper_v r) (wrapper_n r))
      by (apply wrapper_alias_forward_safe; [apply ALIAS; tauto | exact B]).
    destruct UC as [UV VV]. unfold wrapper_unread,unread.
    split; etransitivity; [ | exact UV | | exact VV];
      eapply wrapper_frame_operand_value; [exact ROOT | lia | tauto | exact FRAME | |
        exact ROOT | lia | tauto | exact FRAME | ];
      unfold limb_ptr; apply noverlap_symmetry; rewrite noverlap_mod_idemp_l; apply noverlap_symmetry;
      eapply noverlap_index_r with (index:=8*k) (len2:=8*(chunk_end (wrapper_n r) k));
        [apply SU | unfold chunk_end; nia | apply SV | unfold chunk_end; nia]; lia. }
  assert (RESULT:wrapper_results r (after V_MEM64) (chunk_end (wrapper_n r) k) (chunk_end (wrapper_n r) k)
    ((after V_MEM64) Ⓠ[wrapper_frame r]) ((after V_MEM64) Ⓠ[wrapper_frame r+8])).
  { unfold wrapper_results. rewrite META0,META8,DIFFVALUE. unfold nc_equation in SUMEQ |- *.
    destruct BORROW as [BB EQ]. repeat split; assumption. }
  unfold leaf_abi in ABI. destruct ABI as (ASP & ABX & ABP & A12 & A13 & A14 & A15).
  unfold wrapper_copy_return. exists k. rewrite A13,A14,ABX,ABP,A15,IDX,DIFF,U,V,SUM,(META 24 ltac:(tauto)).
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end].
Qed.
