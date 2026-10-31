(* Use the checked argument packets with the existing CALL/PLT/RET adapters. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_copy_setup.
From Stdlib Require Import NArith.
Import X64Notations.
Open Scope N.

Lemma nextinv_unmarked : forall p I xp t,
  I t=None -> nextinv p I xp false t -> nextinv p I xp true t.
Proof.
  unfold nextinv. intros p I xp t NONE NI EXEC. specialize (NI EXEC).
  inversion NI; subst.
  - apply NIHere'. unfold effinv in *. rewrite NONE in *. exact TRU.
  - eapply NIStep'; [ | exact IL | exact STEP ]. unfold effinv in *. rewrite NONE in *. exact NOI.
Qed.
Lemma wrapper_ready_nc_call : forall sub site ra r cc ac sc s t,
  nc_call_site sub site ra -> models x64typctx s -> wrapper_nc_call_ready s ->
  (forall after tr, nc_resume_post sub (nc_after_call s ra) after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr ra,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr site,s)::t).
Proof.
  intros sub site ra r cc ac sc s t SITE MDL (POS & C & B & U & V & SEP & CELLU & CELLV) CONT.
  apply nextinv_unmarked.
  - destruct sub; cbn [nc_call_site] in SITE;
      destruct SITE as [[A RA]|[[A RA]|[A RA]]]; subst site; reflexivity.
  - eapply nc_wrapper_call; eassumption.
Qed.
Lemma wrapper_ready_copy_call : forall r cc ac sc s t,
  models x64typctx s -> wrapper_copy_call_ready s ->
  (forall after tr, copy_resume_post (copy_after_call s 0x15c5b1) after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
      (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c5b1,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) true ((Addr 0x15c5ac,s)::t).
Proof.
  intros r cc ac sc s t MDL (B & SAFE & SEP & CELL) CONT.
  apply nextinv_unmarked; [reflexivity | ]. eapply copy_wrapper_call; eassumption.
Qed.
