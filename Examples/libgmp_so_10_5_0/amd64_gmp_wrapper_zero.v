(* Zero-limb wrapper correctness through every alias-dispatch route. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family_proofs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_control.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma wrapper_vc_alias_zero : forall r cc ac sc s t,
  wrapper_pre r -> wrapper_n r=0 -> models x64typctx s ->
  wrapper_dispatch r s -> (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c448,s)::t).
Proof.
  intros r cc ac sc s t PRE ZERO MDL DISPATCH ALIAS.
  destruct DISPATCH as [COMMON [UN [SUM [DIFF [U V]]]]].
  pose proof (proj1 (proj2 COMMON)) as LEN.
  unfold wrapper_common in COMMON.
  do 2 x64_step.
  - abstract (split; [exact PRE | ]; split;
      [unfold wrapper_dispatch,wrapper_common; nc_updates; tauto |
       unfold wrapper_route_ok; split; [exact ALIAS | left; apply N.eqb_eq in BC; congruence]]).
  - do 2 x64_step.
    + abstract (split; [exact PRE | ]; split;
        [unfold wrapper_dispatch,wrapper_common; nc_updates; tauto |
         unfold wrapper_route_ok; split; [exact ALIAS | right; apply N.eqb_eq in BC0; congruence]]).
    + x64_step. rewrite ?LEN,ZERO. x64_step. do 2 x64_step.
      split; [exact PRE | ]. apply wrapper_zero_common; [ | exact ZERO | ].
      * unfold wrapper_common. nc_updates. destruct COMMON as (SP & N & SAVED & FRAME).
        split; [exact SP | ]. split; [symmetry; exact ZERO | ]. split; assumption.
      * nc_updates. rewrite N.lxor_nilpotent. reflexivity.
Qed.

Theorem add_n_sub_n_zero_correctness : forall r cc ac sc t s' x',
  startof t (x',s')=(Addr 0x15c360,r) ->
  wrapper_pre r -> wrapper_n r=0 ->
  satisfies_all gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) ((x',s')::t).
Proof.
  intros r cc ac sc t s' x' ENTRY ROOT ZERO.
  apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. split; [exact ROOT | reflexivity].
  - intros t1 a1 s1 t2 UT SPL PRE.
    eapply models_at_invariant.
    + exact (proj1 ROOT).
    + apply gmp_linked_welltyped.
    + rewrite <-(startof_prefix _ _ _ _ _ SPL). exact ENTRY.
    + intro CURRENT.
      assert (EX : gmp_exits 3 cc ac sc (wrapper_property r) ((Addr a1,s1)::t1)=false).
      { unfold get_precondition in PRE.
        destruct (gmp_exits _ _ _ _ _ _) eqn:E; [contradiction | reflexivity]. }
      apply gmp_unchecked_pre in PRE.
      destruct_inv 64 PRE; try discriminate EX;
        cbn [wrapper_property] in PRE; destruct PRE as [ROOTP STATE].
      all: first [
        solve [subst s1; apply wrapper_vc_entry_zero; assumption] |
        solve [destruct STATE as [DISPATCH ALIAS]; eapply wrapper_vc_alias_zero; eassumption] |
        solve [destruct STATE as [DISPATCH SCRATCH]; eapply wrapper_vc_scratch_zero; eassumption] |
        solve [eapply wrapper_vc_epilogue; eassumption] |
        solve [unfold wrapper_loop,wrapper_first_return,wrapper_second_return,wrapper_copy_return in STATE;
          destruct STATE as [k [K REST]]; rewrite ZERO in K; lia]
      ].
Qed.

Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Lemma wrapper_exit_post : forall r cc ac sc pc s t,
  true_inv (get_postcondition gmp_linked
    (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) pc s t) -> wrapper_post r s.
Proof.
  intros r cc ac sc pc s t POST. apply gmp_unchecked_post in POST.
  destruct_inv 64 POST. exact (proj2 POST).
Qed.
