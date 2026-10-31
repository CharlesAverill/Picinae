(* Whole-function wrapper correctness in the explicitly linked IL model.
   The original ELF/PLT binding refinement remains a separate obligation. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family_proofs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_control.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_zero.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_entry.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_dispatch.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_add_header.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_sub_header.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_scratch_header.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_second_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_copy_setup.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_bridge.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_first_returns.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_scratch_first_return.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_second_returns.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_scratch_second_return.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_copy_return.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_add_tail.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_sub_tail.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_scratch_tail.
From Stdlib Require Import NArith Lia.
Import X64Notations.
Open Scope N.

Definition wrapper_header_addr route := match route with
  AdditionFirst => 0x15c3b8 | SubtractionFirst => 0x15c480 | Scratch => 0x15c538 end.
Definition wrapper_first_return_addr route := match route with
  AdditionFirst => 0x15c3ef | SubtractionFirst => 0x15c4b7 | Scratch => 0x15c568 end.

Lemma wrapper_first_call_cut : forall route r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_loop route r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr (wrapper_header_addr route),s)::t).
Proof.
  intros route r cc ac sc s t ROOT MDL LOOP. destruct route.
  - eapply wrapper_vc_add_header; [exact ROOT | exact MDL | exact LOOP | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call false 0x15c3ea 0x15c3ef); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply (wrapper_first_operand_return false r s caller 0x15c3ef after k); eassumption.
  - eapply wrapper_vc_sub_header; [exact ROOT | exact MDL | exact LOOP | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call true 0x15c4b2 0x15c4b7); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply (wrapper_first_operand_return true r s caller 0x15c4b7 after k); eassumption.
  - eapply wrapper_vc_scratch_header; [exact ROOT | exact MDL | exact LOOP | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call false 0x15c563 0x15c568); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply wrapper_scratch_first_return; eassumption.
Qed.

Lemma wrapper_second_call_cut : forall route r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_first_return route r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr (wrapper_first_return_addr route),s)::t).
Proof.
  intros route r cc ac sc s t ROOT MDL FIRST. destruct route.
  - eapply wrapper_vc_add_second_call; [exact ROOT | exact MDL | exact FIRST | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call true 0x15c41b 0x15c420); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply (wrapper_second_operand_return true r s caller 0x15c420 after k); eassumption.
  - eapply wrapper_vc_sub_second_call; [exact ROOT | exact MDL | exact FIRST | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call false 0x15c4e3 0x15c4e8); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply (wrapper_second_operand_return false r s caller 0x15c4e8 after k); eassumption.
  - eapply wrapper_vc_scratch_second_call; [exact ROOT | exact MDL | exact FIRST | ].
    intros k caller tr K CURRENT DATA READY.
    eapply (wrapper_ready_nc_call true 0x15c592 0x15c597); [vm_compute; tauto | exact CURRENT | exact READY | ].
    intros after tl POST. x64_step. split; [exact ROOT | ].
    eapply wrapper_scratch_second_return; eassumption.
Qed.

Lemma wrapper_copy_call_cut : forall r cc ac sc s t,
  wrapper_pre r -> models x64typctx s -> wrapper_second_return Scratch r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c597,s)::t).
Proof.
  intros r cc ac sc s t ROOT MDL SECOND.
  eapply wrapper_vc_copy_setup; [exact ROOT | exact MDL | exact SECOND | ].
  intros k caller tr K CURRENT DATA READY.
  eapply wrapper_ready_copy_call; [exact CURRENT | exact READY | ].
  intros after tl POST. x64_step. split; [exact ROOT | ].
  eapply wrapper_copy_return_certificate; eassumption.
Qed.

(* __gmpn_add_n_sub_n precondition *)
(* __gmpn_add_n_sub_n postcondition *)
Theorem add_n_sub_n_functional_correctness : forall r cc ac sc t s' x',
  startof t (x',s')=(Addr 0x15c360,r) -> wrapper_pre r ->
  satisfies_all gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) ((x',s')::t).
Proof.
  intros r cc ac sc t s' x' ENTRY ROOT.
  apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. split; [exact ROOT | reflexivity].
  - intros t1 a1 s1 t2 UT SPL PRE.
    eapply models_at_invariant.
    + exact (proj1 ROOT).
    + apply gmp_linked_welltyped.
    + rewrite <-(startof_prefix _ _ _ _ _ SPL). exact ENTRY.
    + intro CURRENT.
      assert (EX:gmp_exits 3 cc ac sc (wrapper_property r) ((Addr a1,s1)::t1)=false).
      { unfold get_precondition in PRE.
        destruct (gmp_exits _ _ _ _ _ _) eqn:E; [contradiction | reflexivity]. }
      apply gmp_unchecked_pre in PRE.
      destruct_inv 64 PRE; try discriminate EX;
        cbn [wrapper_property] in PRE; destruct PRE as [ROOTP STATE].
      all: first [
        solve [subst s1; destruct (N.eq_dec (wrapper_n r) 0) as [ZERO|POS];
          [apply wrapper_vc_entry_zero; assumption | apply wrapper_vc_entry_positive; [exact ROOT | lia]]] |
        solve [destruct STATE as [DISPATCH ALIAS]; destruct (N.eq_dec (wrapper_n r) 0) as [ZERO|POS];
          [eapply wrapper_vc_alias_zero; eassumption | eapply wrapper_vc_alias_positive; try eassumption; lia]] |
        solve [destruct STATE as [DISPATCH SCRATCH]; destruct (N.eq_dec (wrapper_n r) 0) as [ZERO|POS];
          [eapply wrapper_vc_scratch_zero; eassumption | eapply wrapper_vc_scratch_positive; try eassumption; lia]] |
        solve [eapply (wrapper_first_call_cut AdditionFirst); eassumption] |
        solve [eapply (wrapper_first_call_cut SubtractionFirst); eassumption] |
        solve [eapply (wrapper_first_call_cut Scratch); eassumption] |
        solve [eapply (wrapper_second_call_cut AdditionFirst); eassumption] |
        solve [eapply (wrapper_second_call_cut SubtractionFirst); eassumption] |
        solve [eapply (wrapper_second_call_cut Scratch); eassumption] |
        solve [eapply wrapper_copy_call_cut; eassumption] |
        solve [eapply wrapper_vc_add_tail; eassumption] |
        solve [eapply wrapper_vc_sub_tail; eassumption] |
        solve [eapply wrapper_vc_scratch_tail; eassumption] |
        solve [eapply wrapper_vc_epilogue; eassumption]
      ].
Qed.

(* __gmpn_add_n_sub_n postcondition *)
Corollary add_n_sub_n_post_at_return : forall r cc ac sc t s,
  startof t (Addr 0x15c443,s)=(Addr 0x15c360,r) -> wrapper_pre r ->
  exec_prog gmp_linked ((Addr 0x15c443,s)::t) ->
  unterminated (gmp_exits 3 cc ac sc (wrapper_property r)) t -> wrapper_post r s.
Proof.
  intros r cc ac sc t s ENTRY ROOT EXEC UT.
  pose proof (add_n_sub_n_functional_correctness r cc ac sc t s (Addr 0x15c443) ENTRY ROOT) as ALL.
  pose proof (satall_trueif_inv _ _ _ _ ALL EXEC UT) as POST.
  change (wrapper_pre r /\ wrapper_post r s) in POST. exact (proj2 POST).
Qed.
