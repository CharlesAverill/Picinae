(* The first scratch-route call returns a buffered sum and preserves inputs. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_header_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_return_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma wrapper_scratch_first_return : forall r before caller ra after k,
  wrapper_pre r -> models x64typctx caller -> k<wrapper_n r ->
  wrapper_loop Scratch r before -> wrapper_header_data Scratch r before caller k ->
  nc_resume_post false (nc_after_call caller ra) after -> wrapper_first_return Scratch r after.
Proof.
  intros r before caller ra after k PRE MDL K LOOP DATA POST.
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & PTRS).
  destruct LOOP as (j & J & JM & COMMON & ROUTE & REGS & UN & RESULT).
  destruct REGS as (U & V & INDEX & DIFF & SUMCELL & SCRATCHCELL).
  assert (j=k) by congruence. subst j. rewrite OLDK in *. rewrite N.add_0_r in RESULT.
  change (caller V_MEM64=before V_MEM64) in MEM.
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  assert (CC:wrapper_common r caller).
  { unfold wrapper_common in COMMON |- *. rewrite MEM. split; [exact SP | ]. split; [exact LEN | ]. tauto. }
  pose proof (nc_resume_frame false r caller ra after PRE MDL SP POST) as [ABI FRAME].
  rewrite DI,CX in FRAME.
  pose proof (wrapper_common_scratch_result r caller after (chunk_size (wrapper_n r) k) PRE QB CC ABI FRAME) as COMMON'.
  assert (SU:~overlap 64 (caller R_RSI) (8*caller R_RCX) (caller R_RSP ⊖ 8) 8).
  { rewrite SI,CX,SP. eapply wrapper_operand_call_cell; [exact PRE | tauto | exact END]. }
  assert (SV:~overlap 64 (caller R_RDX) (8*caller R_RCX) (caller R_RSP ⊖ 8) 8).
  { rewrite DX,CX,SP. eapply wrapper_operand_call_cell; [exact PRE | tauto | exact END]. }
  pose proof (nc_resume_original_inputs false caller ra after SU SV POST) as [BIT EQ].
  rewrite DI,SI,DX,CX,CI,MEM,!value_limb_ptr in EQ.
  pose proof (wrapper_chunk_inputs r (before V_MEM64) k K UN) as [UV VV]. rewrite UV,VV in EQ.
  assert (SUMLOW:value (after V_MEM64) (wrapper_sum r) k=value (before V_MEM64) (wrapper_sum r) k).
  { rewrite <-(MEM). eapply wrapper_frame_scratch_prefix; [exact PRE | exact QB | lia | tauto | exact FRAME]. }
  assert (DIFFLOW:value (after V_MEM64) (wrapper_diff r) k=value (before V_MEM64) (wrapper_diff r) k).
  { rewrite <-(MEM). eapply wrapper_frame_scratch_prefix; [exact PRE | exact QB | lia | tauto | exact FRAME]. }
  assert (META:forall offset, offset+8<=32 ->
    (after V_MEM64) Ⓠ[wrapper_frame r+offset]=(before V_MEM64) Ⓠ[wrapper_frame r+offset]).
  { intros offset OFF. rewrite <-(MEM). eapply wrapper_frame_scratch_metadata; eassumption. }
  pose proof (META 0 ltac:(lia)) as META0. rewrite N.add_0_r in META0.
  assert (UN':wrapper_unread r (after V_MEM64) k).
  { eapply (wrapper_frame_scratch_unread r (caller V_MEM64) (after V_MEM64) (chunk_size (wrapper_n r) k) k); [exact PRE | exact QB | lia | rewrite MEM; exact UN | exact FRAME]. }
  assert (BUFFER:wrapper_scratch_sum r (after V_MEM64) k (chunk_size (wrapper_n r) k) (after R_RAX)).
  { split; [exact BIT | ]. rewrite !value_add,SUMLOW.
    eapply nc_append; [ | exact EQ ]. unfold wrapper_results in RESULT.
    tauto. }
  assert (PREFIX:wrapper_results r (after V_MEM64) k k
    ((after V_MEM64) Ⓠ[wrapper_frame r]) ((after V_MEM64) Ⓠ[wrapper_frame r+8])).
  { unfold wrapper_results. rewrite SUMLOW,DIFFLOW,META0,(META 8 ltac:(lia)). exact RESULT. }
  unfold leaf_abi in ABI. destruct ABI as (ASP & ABX & ABP & A12 & A13 & A14 & A15).
  unfold wrapper_first_return. exists k. rewrite ABX,ABP,BX,BP,A13,A14,A15.
  destruct PTRS as (IX & DF & COUNT). rewrite IX,DF,COUNT,(META 16 ltac:(lia)),(META 24 ltac:(lia)).
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end].
Qed.
