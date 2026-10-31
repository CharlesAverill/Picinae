(* Scratch subtraction return through the concrete copy CALL site. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Definition wrapper_copy_call_data r (before s : store) k :=
  before R_R15=chunk_size (wrapper_n r) k /\ before R_R13=k+170 /\
  s V_MEM64=(before V_MEM64)[Ⓠwrapper_frame r+8:=before R_RAX] /\
  s R_RSP=wrapper_frame r /\ s R_R12=wrapper_n r /\
  s R_RDI=limb_ptr (wrapper_sum r) k /\ s R_RSI=wrapper_frame r+32 /\
  s R_RDX=chunk_size (wrapper_n r) k /\ s R_R13=k+170 /\
  s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
  s R_RBX=limb_ptr (wrapper_u r) (k+170) /\ s R_RBP=limb_ptr (wrapper_v r) (k+170) /\
  s R_R15=limb_ptr (wrapper_sum r) k.
(* __gmpn_copyi precondition *)
Definition wrapper_copy_call_ready (s : store) :=
  8*s R_RDX<=2^64 /\ forward_safe (s R_RDI) (s R_RSI) (s R_RDX) /\
  ~overlap 64 (s R_RSP ⊖ 8) 8 (s R_RDI) (8*s R_RDX) /\
  ~overlap 64 (s R_RSI) (8*s R_RDX) (s R_RSP ⊖ 8) 8.
Lemma wrapper_copy_ready : forall r before s k,
  wrapper_pre r -> k<wrapper_n r -> wrapper_copy_call_data r before s k ->
  wrapper_copy_call_ready s.
Proof.
  intros r before s k PRE K (COUNT & OLDIDX & MEM & SP & LEN & DI & SI & DX & REST).
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  unfold wrapper_copy_call_ready. rewrite DI,SI,DX,SP.
  split; [nia | ]. split.
  - apply forward_safe_disjoint64. unfold array_separate.
    replace (wrapper_frame r+32) with (wrapper_stack r+40) by (unfold wrapper_frame,wrapper_stack; lia).
    eapply noverlap_index_r; [eapply wrapper_operand_stack; [exact PRE | tauto | exact END] | nia].
  - split; [apply noverlap_symmetry; eapply wrapper_operand_call_cell; [exact PRE | tauto | exact END] | ].
    rewrite wrapper_call_cell by exact PRE. apply noverlap_symmetry.
    replace (wrapper_frame r+32) with (wrapper_stack r+8+32) by (unfold wrapper_frame,wrapper_stack; lia).
    eapply noverlap_index_r with (len2:=32+8*chunk_size (wrapper_n r) k).
    + apply noverlap_adjacent64. nia.
    + nia.
Qed.

Lemma wrapper_vc_copy_setup : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_second_return Scratch r s ->
  (forall k after tr, k<wrapper_n r -> models x64typctx after ->
    wrapper_copy_call_data r s after k -> wrapper_copy_call_ready after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c5ac,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c597,s)::t).
Proof.
  intros r cc ac sc s t PRE MDL SECOND CONT.
  destruct SECOND as (k & K & KM & COMMON & ROUTE & UN & U & V & IDX & DIFF & COUNT & SUM & SCRATCH & REST).
  pose proof (proj1 COMMON) as SP. pose proof (proj1 (proj2 COMMON)) as LEN.
  assert (SUMP:(s V_MEM64) Ⓠ[16+wrapper_frame r]=limb_ptr (wrapper_sum r) k)
    by (rewrite N.add_comm; exact SUM).
  assert (SCRATCHP:(s V_MEM64) Ⓠ[24+wrapper_frame r]=wrapper_frame r+32)
    by (rewrite N.add_comm; exact SCRATCH).
  do 5 x64_step.
  eapply models_after_steps; [exact MDL | apply gmp_linked_welltyped | ]. intro CURRENT.
  match goal with |- nextinv _ _ _ _ ((Addr _,?after)::_) =>
    assert (DATA:wrapper_copy_call_data r s after k) by
      (abstract (unfold wrapper_copy_call_data; nc_updates; psimpl;
        replace (8+wrapper_frame r) with (wrapper_frame r+8) by lia;
        repeat first [reflexivity | assumption | solve [lia] | match goal with |- _ /\ _ => split end]));
    eapply CONT; [exact K | exact CURRENT | exact DATA | eapply wrapper_copy_ready; eassumption]
  end.
Qed.
