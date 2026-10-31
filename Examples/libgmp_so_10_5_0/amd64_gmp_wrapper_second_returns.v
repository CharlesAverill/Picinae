(* Second-call return certificates for the two direct-output routes. *)
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
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_first_returns.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma wrapper_first_operand_prefixes : forall sub r before k,
  wrapper_first_return (first_operand_route (negb sub)) r before ->
  (if sub then before R_R14 else before R_R13)=k+170 ->
  k mod 170=0 /\ wrapper_common r before /\
  wrapper_route_ok (first_operand_route (negb sub)) r /\ wrapper_unread r (before V_MEM64) k /\
  wrapper_prefix sub r (before V_MEM64) (operand_dst sub r) k ((before V_MEM64) Ⓠ[wrapper_frame r+8]) /\
  wrapper_prefix (negb sub) r (before V_MEM64) (operand_dst (negb sub) r) (chunk_end (wrapper_n r) k) (before R_RAX) /\
  before R_RAX<=1 /\ (before V_MEM64) Ⓠ[wrapper_frame r+8]<=1.
Proof.
  intros sub r before k FIRST IDX. destruct sub;
    destruct FIRST as (j & J & JM & COMMON & ROUTE & UN & U & V & INDEX & P1 & P2 & COUNT & RESULT);
    assert (JK:j=k) by lia; rewrite JK in *;
    unfold wrapper_results,wrapper_prefix,operand_dst in *;
    cbn [first_operand_route negb] in *; tauto.
Qed.
Lemma wrapper_second_operand_return : forall sub r before caller ra after k,
  wrapper_pre r -> models x64typctx caller -> k<wrapper_n r ->
  wrapper_first_return (first_operand_route (negb sub)) r before ->
  wrapper_second_call_data (first_operand_route (negb sub)) r before caller k ->
  nc_resume_post sub (nc_after_call caller ra) after ->
  wrapper_second_return (first_operand_route (negb sub)) r after.
Proof.
  intros sub r before caller ra after k PRE MDL K FIRST DATA POST.
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & PTRS).
  assert (D:operand_dst sub r=wrapper_sum r \/ operand_dst sub r=wrapper_diff r)
    by (destruct sub; [right | left]; reflexivity).
  assert (OTHERD:operand_dst (negb sub) r=wrapper_sum r \/ operand_dst (negb sub) r=wrapper_diff r)
    by (destruct sub; [left | right]; reflexivity).
  assert (DI':caller R_RDI=limb_ptr (operand_dst sub r) k) by (destruct sub; exact DI).
  clear DI. rename DI' into DI.
  assert (OLDK':(if sub then before R_R14 else before R_R13)=k+170) by (destruct sub; exact OLDK).
  pose proof (wrapper_first_operand_prefixes sub r before k FIRST OLDK')
    as (KM & COMMON & ROUTE & UN & PREFIX & OTHER & FIRSTBIT & BIT).
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  fold (chunk_end (wrapper_n r) k) in END.
  pose proof (wrapper_common_metadata r before 0 (before R_RAX) PRE ltac:(lia) COMMON) as CBASE.
  rewrite N.add_0_r in CBASE.
  assert (CC:wrapper_common r caller).
  { unfold wrapper_common in CBASE |- *. nc_updates.
    repeat (rewrite update_updated in CBASE || rewrite update_frame in CBASE by discriminate).
    rewrite MEM. split; [exact SP | ]. split; [exact LEN | ]. tauto. }
  assert (UC:wrapper_unread r (caller V_MEM64) k).
  { rewrite MEM. pose proof (wrapper_unread_metadata r (before V_MEM64) 0 (before R_RAX) k PRE ltac:(lia) ltac:(lia) UN) as H.
    rewrite N.add_0_r in H. exact H. }
  assert (PC:wrapper_prefix sub r (caller V_MEM64) (operand_dst sub r) k (caller R_R8)).
  { unfold wrapper_prefix in PREFIX |- *. rewrite MEM,CI.
    replace (wrapper_frame r) with (wrapper_frame r+0) at 1 by lia.
    rewrite wrapper_metadata_array by (try assumption; tauto || lia). exact PREFIX. }
  pose proof (wrapper_chunk_result sub r caller ra after (operand_dst sub r) k
    (chunk_size (wrapper_n r) k) PRE MDL END D SP DI SI DX CX UC PC POST) as [OUTBIT OUTEQ].
  fold (chunk_end (wrapper_n r) k) in OUTEQ.
  pose proof (nc_resume_frame sub r caller ra after PRE MDL SP POST) as [ABI FRAME].
  rewrite DI,CX in FRAME.
  pose proof (wrapper_common_result r caller after (operand_dst sub r) k
    (chunk_size (wrapper_n r) k) PRE END D CC ABI FRAME) as COMMON'.
  assert (SEP:array_separate (operand_dst (negb sub) r) (operand_dst sub r) (wrapper_n r)).
  { pose proof (proj1 (proj2 (proj2 (proj2 (proj2 PRE))))) as H.
    destruct sub; [exact H | apply noverlap_symmetry,H]. }
  assert (OP:wrapper_prefix (negb sub) r (after V_MEM64) (operand_dst (negb sub) r)
    (chunk_end (wrapper_n r) k) (before R_RAX)).
  { unfold wrapper_prefix in OTHER |- *.
    rewrite (wrapper_frame_prefix_value r (caller V_MEM64) (after V_MEM64)
      (operand_dst sub r) k (chunk_size (wrapper_n r) k) (operand_dst (negb sub) r)
      (chunk_end (wrapper_n r) k) PRE END END OTHERD SEP FRAME),MEM.
    replace (wrapper_frame r) with (wrapper_frame r+0) at 1 by lia.
    rewrite wrapper_metadata_array by (try assumption; tauto || lia). exact OTHER. }
  assert (UN':wrapper_unread r (after V_MEM64) (chunk_end (wrapper_n r) k)).
  { eapply wrapper_frame_unread_advance; [exact PRE | exact END | exact D | exact UC | exact FRAME]. }
  assert (META0:(after V_MEM64) Ⓠ[wrapper_frame r]=before R_RAX).
  { pose proof (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (operand_dst sub r)
      k (chunk_size (wrapper_n r) k) 0 PRE END ltac:(lia) D FRAME) as H.
    rewrite N.add_0_r in H. rewrite H,MEM,getmem_setmem by (vm_compute; easy).
    apply N.mod_small; lia. }
  unfold leaf_abi in ABI. destruct ABI as (ASP & ABX & ABP & A12 & A13 & A14 & A15).
  destruct sub; cbn [first_operand_route operand_dst negb] in *;
    unfold wrapper_second_return; exists k;
    rewrite META0,ABX,ABP,BX,BP,A13,A14,A15;
    destruct PTRS as (INDEX & PTR1 & PTR2); rewrite INDEX,PTR1,PTR2;
    repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end |
      solve [unfold wrapper_results,wrapper_prefix in *; tauto]].
Qed.
