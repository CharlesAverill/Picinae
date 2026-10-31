(* Reviewable caller states at the first arithmetic CALL of each chunk. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.
Definition wrapper_first_site route := match route with
  AdditionFirst => 0x15c3ea | SubtractionFirst => 0x15c4b2 | Scratch => 0x15c563 end.
Definition wrapper_header_memory route r (before : store) k :=
  match route with Scratch => before V_MEM64 | _ =>
    (before V_MEM64)[Ⓠwrapper_frame r+16:=chunk_size (wrapper_n r) k] end.
Definition wrapper_header_data route r (before s : store) k :=
  (match route with AdditionFirst => before R_R14 | _ => before R_R13 end)=k /\
  s V_MEM64=wrapper_header_memory route r before k /\
  s R_RSP=wrapper_frame r /\ s R_R12=wrapper_n r /\
  s R_RDI=(match route with AdditionFirst => limb_ptr (wrapper_sum r) k |
    SubtractionFirst => limb_ptr (wrapper_diff r) k | Scratch => wrapper_frame r+32 end) /\
  s R_RSI=limb_ptr (wrapper_u r) k /\ s R_RDX=limb_ptr (wrapper_v r) k /\
  s R_RCX=chunk_size (wrapper_n r) k /\ s R_R8=(before V_MEM64) Ⓠ[wrapper_frame r] /\
  s R_RBX=limb_ptr (wrapper_u r) k /\ s R_RBP=limb_ptr (wrapper_v r) k /\
  match route with
  | AdditionFirst => s R_R14=k+170 /\ s R_R13=limb_ptr (wrapper_sum r) (k+170) /\
      s R_R15=limb_ptr (wrapper_diff r) k
  | SubtractionFirst => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
      s R_R15=limb_ptr (wrapper_sum r) k
  | Scratch => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) k /\
      s R_R15=chunk_size (wrapper_n r) k
  end.

Lemma wrapper_header_ready : forall route r before s k,
  wrapper_pre r -> k<wrapper_n r -> wrapper_loop route r before ->
  wrapper_header_data route r before s k -> wrapper_nc_call_ready s.
Proof.
  intros route r before s k PRE K LOOP DATA.
  destruct LOOP as (j & J & JM & COMMON & ROUTE & REGS & UN & RESULT).
  assert (C:(before V_MEM64) Ⓠ[wrapper_frame r]<=1).
  { destruct route; unfold wrapper_results in RESULT; rewrite ?N.add_0_r in RESULT; tauto. }
  destruct DATA as (OLDK & MEM & SP & LEN & DI & SI & DX & CX & CI & BX & BP & SAVED).
  destruct route.
  - eapply wrapper_nc_operands_ready; [exact PRE | exact K | exact C | left; reflexivity | eassumption ..].
  - eapply wrapper_nc_operands_ready; [exact PRE | exact K | exact C | right; reflexivity | eassumption ..].
  - eapply (wrapper_nc_scratch_ready r s k ((before V_MEM64) Ⓠ[wrapper_frame r])); eassumption.
Qed.
