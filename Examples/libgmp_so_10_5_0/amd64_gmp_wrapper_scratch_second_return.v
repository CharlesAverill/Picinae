(* Scratch subtraction commits its chunk while retaining the buffered sum. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_next_call_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_return_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma wrapper_scratch_second_return : forall r before caller ra after k,
  wrapper_pre r -> models x64typctx caller -> k<wrapper_n r ->
  wrapper_first_return Scratch r before -> wrapper_second_call_data Scratch r before caller k ->
  nc_resume_post true (nc_after_call caller ra) after -> wrapper_second_return Scratch r after.
Proof.
  intros r before caller ra after k PRE MDL K FIRST DATA POST.
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & PTRS).
  destruct FIRST as (j & J & JM & COMMON & ROUTE & UN & U & V & INDEX & DIFF & COUNT & SUMCELL & SCRATCHCELL & RESULT & BUFFER).
  assert (JK:j=k) by lia. rewrite JK in *.
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  pose proof (wrapper_common_metadata r before 0 (before R_RAX) PRE ltac:(lia) COMMON) as CBASE.
  rewrite N.add_0_r in CBASE.
  assert (CC:wrapper_common r caller).
  { unfold wrapper_common in CBASE |- *. nc_updates.
    repeat (rewrite update_updated in CBASE || rewrite update_frame in CBASE by discriminate).
    rewrite MEM. split; [exact SP | ]. split; [exact LEN | ]. tauto. }
  assert (UC:wrapper_unread r (caller V_MEM64) k).
  { rewrite MEM. pose proof (wrapper_unread_metadata r (before V_MEM64) 0 (before R_RAX) k PRE ltac:(lia) ltac:(lia) UN) as H.
    rewrite N.add_0_r in H. exact H. }
  assert (PC:wrapper_prefix true r (caller V_MEM64) (wrapper_diff r) k (caller R_R8)).
  { unfold wrapper_prefix. rewrite MEM,CI.
    replace (wrapper_frame r) with (wrapper_frame r+0) at 1 by lia.
    rewrite wrapper_metadata_array by (try assumption; tauto || lia).
    unfold wrapper_results in RESULT. tauto. }
  pose proof (wrapper_chunk_result true r caller ra after (wrapper_diff r) k
    (chunk_size (wrapper_n r) k) PRE MDL END ltac:(tauto) SP DI SI DX CX UC PC POST) as [OUTBIT OUTEQ].
  fold (chunk_end (wrapper_n r) k) in OUTEQ.
  pose proof (nc_resume_frame true r caller ra after PRE MDL SP POST) as [ABI FRAME].
  rewrite DI,CX in FRAME.
  pose proof (wrapper_common_result r caller after (wrapper_diff r) k
    (chunk_size (wrapper_n r) k) PRE END ltac:(tauto) CC ABI FRAME) as COMMON'.
  assert (UN':wrapper_unread r (after V_MEM64) (chunk_end (wrapper_n r) k)).
  { eapply wrapper_frame_unread_advance; [exact PRE | exact END | right; reflexivity | exact UC | exact FRAME]. }
  assert (SUMLOW:value (after V_MEM64) (wrapper_sum r) k=value (before V_MEM64) (wrapper_sum r) k).
  { rewrite (wrapper_frame_prefix_value r (caller V_MEM64) (after V_MEM64) (wrapper_diff r) k
      (chunk_size (wrapper_n r) k) (wrapper_sum r) k PRE END ltac:(lia) ltac:(tauto)
      (proj1 (proj2 (proj2 (proj2 (proj2 PRE)))) ) FRAME),MEM.
    replace (wrapper_frame r) with (wrapper_frame r+0) at 1 by lia.
    apply wrapper_metadata_array; eassumption || lia || tauto. }
  assert (BUFVALUE:value (after V_MEM64) (wrapper_frame r+32) (chunk_size (wrapper_n r) k)=
    value (before V_MEM64) (wrapper_frame r+32) (chunk_size (wrapper_n r) k)).
  { transitivity (value (caller V_MEM64) (wrapper_frame r+32) (chunk_size (wrapper_n r) k)).
    - apply FRAME.
      + eapply wrapper_stack_operand; [exact PRE | unfold GMPArrayParams.bytes; nia | exact END | tauto].
      + eapply wrapper_stack_call_cell; [exact PRE | unfold GMPArrayParams.bytes; nia].
    - rewrite MEM. apply getmem_noverlap. replace (wrapper_frame r) with (wrapper_frame r+0) at 2 by lia.
      apply noverlap_symmetry. eapply wrapper_scratch_stack_read; [exact PRE | exact QB | lia | left; lia]. }
  assert (META0:(after V_MEM64) Ⓠ[wrapper_frame r]=before R_RAX).
  { pose proof (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (wrapper_diff r)
      k (chunk_size (wrapper_n r) k) 0 PRE END ltac:(lia) ltac:(tauto) FRAME) as H.
    rewrite N.add_0_r in H. rewrite H,MEM,getmem_setmem by (vm_compute; easy).
    apply N.mod_small. pose proof (proj1 BUFFER). lia. }
  assert (META:forall offset, offset=16 \/ offset=24 ->
    (after V_MEM64) Ⓠ[wrapper_frame r+offset]=(before V_MEM64) Ⓠ[wrapper_frame r+offset]).
  { intros offset OFF.
    rewrite (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (wrapper_diff r)
      k (chunk_size (wrapper_n r) k) offset PRE END ltac:(destruct OFF; lia) ltac:(tauto) FRAME),MEM.
    apply getmem_noverlap. apply bounded_cells_separate;
      assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto);
      assert (B:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)); unfold wrapper_frame;
      destruct OFF as [-> | ->]; lia. }
  assert (BUFFER':wrapper_scratch_sum r (after V_MEM64) k (chunk_size (wrapper_n r) k)
      ((after V_MEM64) Ⓠ[wrapper_frame r])).
  { unfold wrapper_scratch_sum. rewrite SUMLOW,BUFVALUE,META0. exact BUFFER. }
  unfold leaf_abi in ABI. destruct ABI as (ASP & ABX & ABP & A12 & A13 & A14 & A15).
  unfold wrapper_second_return. exists k. rewrite ABX,ABP,BX,BP,A13,A14,A15.
  destruct PTRS as (IX & DF & CNT). rewrite IX,DF,CNT,(META 16 ltac:(tauto)),(META 24 ltac:(tauto)).
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end].
Qed.
