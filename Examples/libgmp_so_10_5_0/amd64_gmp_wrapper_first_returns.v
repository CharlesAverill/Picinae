(* First-call return certificates for the two direct-output routes. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_header_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_return_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.
Definition first_operand_route (sub : bool) := if sub then SubtractionFirst else AdditionFirst.
Definition operand_dst (sub : bool) r := if sub then wrapper_diff r else wrapper_sum r.

Lemma wrapper_loop_operand_prefixes : forall sub r before k,
  wrapper_loop (first_operand_route sub) r before ->
  (if sub then before R_R13 else before R_R14)=k ->
  k mod 170=0 /\ wrapper_common r before /\
  wrapper_route_ok (first_operand_route sub) r /\ wrapper_unread r (before V_MEM64) k /\
  wrapper_prefix sub r (before V_MEM64) (operand_dst sub r) k ((before V_MEM64) Ⓠ[wrapper_frame r]) /\
  wrapper_prefix (negb sub) r (before V_MEM64) (operand_dst (negb sub) r) k ((before V_MEM64) Ⓠ[wrapper_frame r+8]) /\
  (before V_MEM64) Ⓠ[wrapper_frame r]<=1 /\ (before V_MEM64) Ⓠ[wrapper_frame r+8]<=1.
Proof.
  intros sub r before k LOOP IDX. destruct sub;
    destruct LOOP as (j & J & JM & COMMON & ROUTE & REGS & UN & RESULT);
    destruct REGS as (U & V & INDEX & PTRS);
    assert (j=k) by congruence; subst j; rewrite IDX in *;
    unfold wrapper_results,wrapper_prefix,operand_dst in *; rewrite ?N.add_0_r in RESULT;
    cbn [first_operand_route negb] in *; rewrite ?N.add_0_r in RESULT; tauto.
Qed.

Lemma wrapper_first_operand_return : forall sub r before caller ra after k,
  wrapper_pre r -> models x64typctx caller -> k<wrapper_n r ->
  wrapper_loop (first_operand_route sub) r before ->
  wrapper_header_data (first_operand_route sub) r before caller k ->
  nc_resume_post sub (nc_after_call caller ra) after ->
  wrapper_first_return (first_operand_route sub) r after.
Proof.
  intros sub r before caller ra after k PRE MDL K LOOP DATA POST.
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & PTRS).
  assert (D:(operand_dst sub r)=wrapper_sum r \/ (operand_dst sub r)=wrapper_diff r)
    by (destruct sub; [right | left]; reflexivity).
  assert (OTHERD:(operand_dst (negb sub) r)=wrapper_sum r \/ (operand_dst (negb sub) r)=wrapper_diff r)
    by (destruct sub; [left | right]; reflexivity).
  assert (DI':caller R_RDI=limb_ptr (operand_dst sub r) k) by (destruct sub; exact DI).
  clear DI. rename DI' into DI.
  assert (OLDK':(if sub then before R_R13 else before R_R14)=k) by (destruct sub; exact OLDK).
  assert (M:caller V_MEM64=(before V_MEM64)[Ⓠwrapper_frame r+16:=chunk_size (wrapper_n r) k]).
  { destruct sub; exact MEM. }
  pose proof (wrapper_loop_operand_prefixes sub r before k LOOP OLDK')
    as (KM & COMMON & ROUTE & UN & PREFIX & OTHER & BIT & OTHERBIT).
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  pose proof (wrapper_common_metadata r before 16 (chunk_size (wrapper_n r) k) PRE ltac:(lia) COMMON) as CBASE.
  assert (CC:wrapper_common r caller).
  { unfold wrapper_common in CBASE |- *. nc_updates.
    repeat (rewrite update_updated in CBASE || rewrite update_frame in CBASE by discriminate).
    rewrite M. split; [exact SP | ]. split; [exact LEN | ]. tauto. }
  assert (UC:wrapper_unread r (caller V_MEM64) k).
  { rewrite M. eapply wrapper_unread_metadata; [exact PRE | lia | lia | exact UN]. }
  assert (PC:wrapper_prefix sub r (caller V_MEM64) (operand_dst sub r) k (caller R_R8)).
  { unfold wrapper_prefix in PREFIX |- *. rewrite M,CI.
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
  assert (OP:wrapper_prefix (negb sub) r (after V_MEM64) (operand_dst (negb sub) r) k
    ((before V_MEM64) Ⓠ[wrapper_frame r+8])).
  { unfold wrapper_prefix in OTHER |- *.
    rewrite (wrapper_frame_prefix_value r (caller V_MEM64) (after V_MEM64)
      (operand_dst sub r) k (chunk_size (wrapper_n r) k) (operand_dst (negb sub) r) k
      PRE END ltac:(lia) OTHERD SEP FRAME),M.
    rewrite wrapper_metadata_array by (try assumption; tauto || lia). exact OTHER. }
  assert (UAF:wrapper_unread r (after V_MEM64) k).
  { eapply wrapper_frame_unread_disjoint; [exact PRE | exact END | | | exact UC | exact FRAME].
    - destruct sub; cbn [first_operand_route] in ROUTE; unfold operand_dst;
        [exact (noverlap_symmetry _ _ _ _ _ (proj1 (proj2 ROUTE))) | exact (noverlap_symmetry _ _ _ _ _ (proj1 ROUTE))].
    - destruct sub; cbn [first_operand_route] in ROUTE; unfold operand_dst;
        [exact (noverlap_symmetry _ _ _ _ _ (proj2 (proj2 ROUTE))) | exact (noverlap_symmetry _ _ _ _ _ (proj2 ROUTE))]. }
  assert (META8:(after V_MEM64) Ⓠ[wrapper_frame r+8]=(before V_MEM64) Ⓠ[wrapper_frame r+8]).
  { rewrite (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (operand_dst sub r)
      k (chunk_size (wrapper_n r) k) 8 PRE END ltac:(lia) D FRAME),M.
    apply getmem_noverlap. apply bounded_cells_separate;
      assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto);
      assert (B:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)); unfold wrapper_frame; lia. }
  assert (META16:(after V_MEM64) Ⓠ[wrapper_frame r+16]=chunk_size (wrapper_n r) k).
  { rewrite (wrapper_frame_metadata r (caller V_MEM64) (after V_MEM64) (operand_dst sub r)
      k (chunk_size (wrapper_n r) k) 16 PRE END ltac:(lia) D FRAME),M.
    rewrite getmem_setmem by (vm_compute; easy). apply N.mod_small; lia. }
  unfold leaf_abi in ABI. destruct ABI as (ASP & ABX & ABP & A12 & A13 & A14 & A15).
  destruct sub; cbn [first_operand_route operand_dst negb] in *;
    unfold wrapper_first_return; exists k;
    rewrite META8,META16,ABX,ABP,BX,BP,A13,A14,A15;
    destruct PTRS as (INDEX & PTR1 & PTR2); rewrite INDEX,PTR1,PTR2;
    repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end |
      solve [unfold wrapper_results,wrapper_prefix in *; tauto]].
Qed.
