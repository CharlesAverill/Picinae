(* States at the second arithmetic CALL and at the scratch-copy CALL. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.
Definition wrapper_second_site route := match route with
  AdditionFirst => 0x15c41b | SubtractionFirst => 0x15c4e3 | Scratch => 0x15c592 end.
Definition wrapper_second_call_data route r (before s : store) k :=
  (match route with AdditionFirst => before R_R14 | _ => before R_R13 end)=k+170 /\
  s V_MEM64=(before V_MEM64)[Ⓠwrapper_frame r:=before R_RAX] /\
  s R_RSP=wrapper_frame r /\ s R_R12=wrapper_n r /\
  s R_RDI=limb_ptr (match route with SubtractionFirst => wrapper_sum r | _ => wrapper_diff r end) k /\
  s R_RSI=limb_ptr (wrapper_u r) k /\ s R_RDX=limb_ptr (wrapper_v r) k /\
  s R_RCX=chunk_size (wrapper_n r) k /\ s R_R8=(before V_MEM64) Ⓠ[wrapper_frame r+8] /\
  s R_RBX=limb_ptr (wrapper_u r) (k+170) /\ s R_RBP=limb_ptr (wrapper_v r) (k+170) /\
  match route with
  | AdditionFirst => s R_R14=k+170 /\ s R_R13=limb_ptr (wrapper_sum r) (k+170) /\
      s R_R15=limb_ptr (wrapper_diff r) (k+170)
  | SubtractionFirst => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
      s R_R15=limb_ptr (wrapper_sum r) (k+170)
  | Scratch => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
      s R_R15=chunk_size (wrapper_n r) k
  end.
Lemma wrapper_second_call_ready : forall route r before s k,
  wrapper_pre r -> k<wrapper_n r -> wrapper_first_return route r before ->
  wrapper_second_call_data route r before s k -> wrapper_nc_call_ready s.
Proof.
  intros route r before s k PRE K FIRST DATA.
  assert (C:(before V_MEM64) Ⓠ[wrapper_frame r+8]<=1).
  { destruct FIRST as (j & J & JM & COMMON & ROUTE & UN & U & V & FIRST).
    destruct route; simpl in FIRST;
      destruct FIRST as (_ & _ & _ & _ & REST).
    - unfold wrapper_results in REST. tauto.
    - unfold wrapper_results in REST. tauto.
    - destruct REST as (_ & POST & SCRATCH). unfold wrapper_results in POST. tauto. }
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & SAVED).
  destruct route.
  - eapply (wrapper_nc_operands_ready r s _ k ((before V_MEM64) Ⓠ[wrapper_frame r+8]));
      [exact PRE | exact K | exact C | right; reflexivity | eassumption ..].
  - eapply (wrapper_nc_operands_ready r s _ k ((before V_MEM64) Ⓠ[wrapper_frame r+8]));
      [exact PRE | exact K | exact C | left; reflexivity | eassumption ..].
  - eapply (wrapper_nc_operands_ready r s _ k ((before V_MEM64) Ⓠ[wrapper_frame r+8]));
      [exact PRE | exact K | exact C | right; reflexivity | eassumption ..].
Qed.
