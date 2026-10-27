(* Memory-frame and AMD64 ABI preservation up to the NC routines' RETs. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_correctness.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Definition nc_frame_invset sub m0 d u v n cin initial :=
  frame_invset (nc_invset sub m0 d u v n cin) initial m0 d n.
Definition nc_call_invset sub m0 d u v n cin initial :=
  inv_conj (nc_invset sub m0 d u v n cin)
    (nc_frame_invset sub m0 d u v n cin initial).
(* __gmpn_add_nc postcondition *)
(* __gmpn_sub_nc postcondition *)
(* __gmpn_add_n postcondition *)
(* __gmpn_sub_n postcondition *)
Definition nc_call_post sub initial m0 d u v n cin s :=
  nc_post sub m0 d u v n cin s /\ leaf_frame initial m0 d n s.

Ltac nc_frame_bound := first [
  match goal with B : ?k + ?q <= ?n |- _ => clear -B; nia end |
  match goal with B : ?n = ?k + ?q |- _ => clear -B; nia end].
Ltac nc_frame_stores :=
  repeat first [assumption |
    match goal with
    |- outside_output ?m0 (setmem 64 LittleE ?size ?m ?a ?out) ?d ?bytes =>
      replace a with (d+(a-d)) by (clear; nia);
      eapply outside_output_store; [nc_frame_bound | ]
    end].
Ltac nc_frame_finish :=
  unfold leaf_frame,leaf_abi;
  psimpl; nc_updates;
  repeat match goal with H : ?s R_RDI = _ |- _ => progress rewrite H end;
  psimpl;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  nc_frame_stores.

Lemma nc_frame_vc : forall sub initial m0 d u v n cin pc s t,
  true_inv (get_precondition (nc_program sub) (nc_invset sub m0 d u v n cin)
    (nc_exit sub) pc s t) ->
  leaf_frame initial m0 d n s ->
  nextinv (nc_program sub) (nc_frame_invset sub m0 d u v n cin initial)
    (nc_exit sub) false ((Addr pc,s)::t).
Proof.
  intros sub initial m0 d u v n cin pc s t PRE FRAME.
  destruct FRAME as [ABI OUT]. unfold leaf_abi in ABI. nc_conj.
  destruct sub; destruct_inv 64 PRE;
    try (lazymatch type of PRE with ex _ =>
      destruct PRE as [k PRE]; unfold nc_stage,nc_ptrs in PRE; nc_conj end);
    cbn [nc_program]; nc_bigstep;
    abstract nc_frame_finish.
Qed.

Theorem nc_call_correctness_from :
  forall sub a s m0 d u v n cin t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub a),s))
    (START : a=0x1284e0 \/ a=0x128500)
    (MDL : models x64typctx s)
    (INITIAL : true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub a),s)::nil)))
    (POS : 0<n) (C : cin<=1) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_call_invset sub m0 d u v n cin s)
    (nc_exit sub) ((x',s')::t).
Proof.
  intros sub a s m0 d u v n cin t s' x' ENTRY START MDL INITIAL POS C B SAFE_U SAFE_V.
  assert (MEM : s V_MEM64=m0).
  { destruct START as [A|A]; subst a; destruct sub;
      cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in INITIAL;
      exact (proj1 INITIAL). }
  assert (FRAME : leaf_frame s m0 d n s).
  { split; [unfold leaf_abi; repeat split; reflexivity | rewrite MEM; apply outside_output_refl]. }
  unfold nc_call_invset. apply prove_invs.
  - simpl. rewrite ENTRY. destruct START as [A|A]; subst a; destruct sub;
      cbn [nc_program nc_address]; x64_step; split; assumption.
  - intros t1 a1 s1 t2 UT SPL PRE.
    eapply models_at_invariant.
    + exact MDL.
    + apply nc_welltyped.
    + rewrite <-(startof_prefix _ _ _ _ _ SPL). exact ENTRY.
    + intro CURRENT. clear -CURRENT PRE POS C B SAFE_U SAFE_V.
      destruct sub; destruct_inv 64 PRE; destruct PRE as [ARITH FRAME];
        (eapply nextinv_conj;
        [ apply frame_invset_support
        | nc_discharge_cut CURRENT POS C B SAFE_U SAFE_V ARITH
        | eapply nc_frame_vc; [exact ARITH | exact FRAME] ]).
Qed.

(* __gmpn_add_nc precondition *)
(* __gmpn_sub_nc precondition *)
Theorem nc_call_correctness :
  forall sub s m0 d u v n cin t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub 0x1284e0),s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m0) (DST : s R_RDI=d) (SRC_U : s R_RSI=u)
    (SRC_V : s R_RDX=v) (LEN : s R_RCX=n) (CIN : s R_R8=cin)
    (POS : 0<n) (C : cin<=1) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_call_invset sub m0 d u v n cin s)
    (nc_exit sub) ((x',s')::t).
Proof.
  intros. eapply nc_call_correctness_from; try eassumption.
  - left. reflexivity.
  - destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv];
      repeat split; assumption.
Qed.

(* __gmpn_add_n precondition *)
(* __gmpn_sub_n precondition *)
Theorem nc_plain_call_correctness :
  forall sub s m0 d u v n t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub 0x128500),s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m0) (DST : s R_RDI=d) (SRC_U : s R_RSI=u)
    (SRC_V : s R_RDX=v) (LEN : s R_RCX=n)
    (POS : 0<n) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_call_invset sub m0 d u v n 0 s)
    (nc_exit sub) ((x',s')::t).
Proof.
  intros. eapply nc_call_correctness_from; try eassumption.
  - right. reflexivity.
  - destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv];
      repeat split; try assumption; reflexivity.
  - vm_compute; easy.
Qed.

Definition add_nc_call_correctness := nc_call_correctness false.
Definition sub_nc_call_correctness := nc_call_correctness true.
Definition add_n_call_correctness := nc_plain_call_correctness false.
Definition sub_n_call_correctness := nc_plain_call_correctness true.

Lemma nc_call_exit_post : forall sub a initial m0 d u v n cin s t,
  (a=0x128526 \/ a=0x12853f \/ a=0x12855d \/ a=0x1285d4) ->
  true_inv (nc_call_invset sub m0 d u v n cin initial ((Addr (nc_address sub a),s)::t)) ->
  nc_call_post sub initial m0 d u v n cin s.
Proof.
  intros sub a initial m0 d u v n cin s t CASE POST.
  destruct CASE as [A|[A|[A|A]]]; subst a; destruct sub; exact POST.
Qed.
