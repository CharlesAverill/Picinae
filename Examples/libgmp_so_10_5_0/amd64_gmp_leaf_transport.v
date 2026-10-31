(* Checked adapters from the standalone leaf programs to the linked program. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_correctness.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_program_transport.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
From Stdlib Require Import NArith Lia.
Import X64Notations.
Open Scope N.

Lemma gmp_extends_nc : forall sub, program_extends (nc_program sub) gmp_linked.
Proof.
  intros [] s a code LOOK; cbn [nc_program] in LOOK.
  - rewrite gmp_linked_sub_nc; [exact LOOK | rewrite LOOK; discriminate].
  - rewrite gmp_linked_add_nc; [exact LOOK | rewrite LOOK; discriminate].
Qed.
Lemma gmp_extends_copyi : program_extends libgmp_so_10_5_0___gmpn_copyi_amd64 gmp_linked.
Proof.
  intros s a code LOOK. rewrite gmp_linked_copyi; [exact LOOK | rewrite LOOK; discriminate].
Qed.

Lemma nc_call_supported : forall sub m0 d u v n cin initial,
  inv_supported (nc_program sub) (nc_call_invset sub m0 d u v n cin initial).
Proof.
  intros sub m0 d u v n cin initial [|[[pc|e] s] tl]; try reflexivity.
  intro LOOK. destruct sub.
  - destruct (N.lt_ge_cases pc 0x260) as [LOW|HIGH].
    + assert (Z : pc-0x260=0) by lia.
      unfold nc_call_invset,inv_conj,nc_frame_invset,frame_invset,
        nc_invset,nc_aux_invset,nc_invset_core. rewrite Z. reflexivity.
    + set (a:=pc-0x260).
      assert (PC : pc=a+0x260) by (unfold a; lia).
      rewrite PC in LOOK |- *. clearbody a.
      unfold nc_call_invset,inv_conj,nc_frame_invset,frame_invset,
        nc_invset,nc_aux_invset,nc_invset_core.
      rewrite !N.add_sub.
      destruct a as [|a];
        repeat first [reflexivity | solve [discriminate LOOK] | destruct a as [a|a|] ].
  - unfold nc_call_invset,inv_conj,nc_frame_invset,frame_invset,
      nc_invset,nc_aux_invset,nc_invset_core.
    destruct pc as [|pc];
      repeat first [reflexivity | solve [discriminate LOOK] | destruct pc as [pc|pc|] ].
Qed.
Lemma copyi_call_supported : forall m0 d u n initial,
  inv_supported libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_call_invset m0 d u n initial).
Proof.
  intros m0 d u n initial [|[[pc|e] s] tl]; try reflexivity.
  intro LOOK. unfold copyi_call_invset,inv_conj,copyi_frame_invset,frame_invset,copyi_invset.
  destruct pc as [|pc];
    repeat first [reflexivity | solve [discriminate LOOK] | destruct pc as [pc|pc|] ].
Qed.
Lemma nc_call_head : forall sub m0 d u v n cin initial,
  head_invariant (nc_call_invset sub m0 d u v n cin initial).
Proof. intros sub m0 d u v n cin initial [[a|e] s] t1 t2; reflexivity. Qed.
Lemma nc_exit_head : forall sub, head_exit (nc_exit sub).
Proof. intros sub [[a|e] s] t1 t2; reflexivity. Qed.
Lemma copyi_call_head : forall m0 d u n initial,
  head_invariant (copyi_call_invset m0 d u n initial).
Proof. intros m0 d u n initial [[a|e] s] t1 t2; reflexivity. Qed.
Lemma copyi_exit_head : head_exit copyi_exit.
Proof. intros [[a|e] s] t1 t2; reflexivity. Qed.

Lemma nc_call_vc : forall sub initial m0 d u v n cin pc s t,
  models x64typctx s -> 0<n -> cin<=1 -> 8*n<=2^64 ->
  GMPArrays.forward_safe d u n -> GMPArrays.forward_safe d v n ->
  true_inv (get_precondition (nc_program sub) (nc_call_invset sub m0 d u v n cin initial)
    (nc_exit sub) pc s t) ->
  nextinv (nc_program sub) (nc_call_invset sub m0 d u v n cin initial)
    (nc_exit sub) false ((Addr pc,s)::t).
Proof.
  intros sub initial m0 d u v n cin pc s t MDL POS C B SAFE_U SAFE_V PRE.
  unfold nc_call_invset in *. destruct sub; destruct_inv 64 PRE; destruct PRE as [ARITH FRAME];
    (eapply nextinv_conj;
     [ apply frame_invset_support
     | nc_discharge_cut MDL POS C B SAFE_U SAFE_V ARITH
     | eapply nc_frame_vc; [exact ARITH | exact FRAME] ]).
Qed.
Lemma copyi_call_vc : forall initial m0 d u n pc s t,
  d<2^64 -> u<2^64 -> n<2^64 -> GMP64.forward_safe d u n ->
  true_inv (get_precondition libgmp_so_10_5_0___gmpn_copyi_amd64
    (copyi_call_invset m0 d u n initial) copyi_exit pc s t) ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_call_invset m0 d u n initial)
    copyi_exit false ((Addr pc,s)::t).
Proof.
  intros initial m0 d u n pc s t D64 U64 N64 SAFE PRE.
  unfold copyi_call_invset in *. destruct_inv 64 PRE; destruct PRE as [ARITH FRAME];
    (eapply nextinv_conj;
     [ apply frame_invset_support
     | copyi_arithmetic_cut D64 U64 N64 SAFE ARITH
     | eapply copyi_frame_vc; [exact ARITH | exact FRAME] ]).
Qed.
