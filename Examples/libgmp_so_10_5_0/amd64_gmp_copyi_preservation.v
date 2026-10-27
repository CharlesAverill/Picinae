(* Copy correctness with pre-RET ABI and protected-memory guarantees. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMP64.
Open Scope N.

Definition copyi_frame_invset m0 d u n initial :=
  frame_invset (copyi_invset m0 d u n) initial m0 d n.
Definition copyi_call_invset m0 d u n initial :=
  inv_conj (copyi_invset m0 d u n) (copyi_frame_invset m0 d u n initial).
(* __gmpn_copyi postcondition *)
Definition copyi_call_post initial m0 d u n s :=
  s V_MEM64=copied m0 d u n /\ leaf_frame initial m0 d n s.

Ltac copy_frame_updates := repeat (rewrite update_updated || rewrite update_frame by discriminate).
Ltac copy_frame_conj := repeat match goal with H : ?T |- _ =>
  lazymatch T with ?f ?a ?b => constr_eq f and; destruct H end end.
Ltac copy_frame_bound := first [
  match goal with B : ?k + ?q <= ?n |- _ => clear -B; nia end |
  match goal with B : ?k <= ?n, E : ?n-?k = ?q |- _ => clear -B E; nia end].
Ltac copy_frame_finish :=
  unfold leaf_frame,leaf_abi; psimpl; copy_frame_updates;
  repeat match goal with H : ?s R_RDI = _ |- _ => progress rewrite H end; psimpl;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  repeat first [assumption |
    match goal with
    |- outside_output ?m0 (setmem 64 LittleE ?size ?m ?a ?out) ?d ?bytes =>
      replace a with (d+(a-d)) by (clear; nia);
      eapply outside_output_store; [copy_frame_bound | ]
    end].

Lemma copyi_frame_vc : forall initial m0 d u n pc s t,
  true_inv (get_precondition libgmp_so_10_5_0___gmpn_copyi_amd64
    (copyi_invset m0 d u n) copyi_exit pc s t) ->
  leaf_frame initial m0 d n s ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64
    (copyi_frame_invset m0 d u n initial) copyi_exit false ((Addr pc,s)::t).
Proof.
  intros initial m0 d u n pc s t PRE FRAME.
  destruct FRAME as [ABI OUT]. unfold leaf_abi in ABI. copy_frame_conj.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [DI [SI LEN]]].
    libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep; abstract copy_frame_finish.
  - destruct PRE as [k [[MEM [SI DI]] [KN LEN]]].
    libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep; abstract copy_frame_finish.
  - destruct PRE as [k [[MEM [SI DI]] [KN [REM LEN]]]].
    assert (CASE : n-k=0 \/ n-k=1 \/ n-k=2 \/ n-k=3) by (clear -REM; lia).
    destruct CASE as [E|[E|[E|E]]]; rewrite E in LEN;
      libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep;
      rewrite ?LEN in *; try discriminate; abstract copy_frame_finish.
  - destruct PRE as [k [[MEM [SI DI]] [KN [CASE LEN]]]].
    destruct CASE as [E|E]; rewrite E in LEN;
      libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep;
      rewrite ?LEN in *; try discriminate; abstract copy_frame_finish.
Qed.

Ltac copyi_arithmetic_cut D64 U64 N64 SAFE PRE := first [
  solve [destruct PRE as [MEM [DI [SI LEN]]]; eapply copyi_vc_entry; eassumption] |
  solve [eapply copyi_vc_loop; eassumption] |
  solve [eapply copyi_vc_tail1; eassumption] |
  solve [eapply copyi_vc_tail2; eassumption] ].

(* __gmpn_copyi precondition *)
Theorem copyi_call_correctness :
  forall s d u n m0 t s' x'
    (ENTRY : startof t (x',s')=(Addr 0x15b186,s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m0) (DST : s R_RDI=d) (SRC : s R_RSI=u) (LEN : s R_RDX=n)
    (SAFE : forward_safe d u n),
  satisfies_all libgmp_so_10_5_0___gmpn_copyi_amd64
    (copyi_call_invset m0 d u n s) copyi_exit ((x',s')::t).
Proof.
  intros.
  assert (D64 : d<2^64) by (pose proof (models_var R_RDI MDL) as H; rewrite DST in H; exact H).
  assert (U64 : u<2^64) by (pose proof (models_var R_RSI MDL) as H; rewrite SRC in H; exact H).
  assert (N64 : n<2^64) by (pose proof (models_var R_RDX MDL) as H; rewrite LEN in H; exact H).
  assert (FRAME : leaf_frame s m0 d n s).
  { split; [unfold leaf_abi; repeat split; reflexivity | rewrite MEM; apply outside_output_refl]. }
  unfold copyi_call_invset. apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. split; [repeat split; assumption | exact FRAME].
  - intros. clear -PRE D64 U64 N64 SAFE.
    destruct_inv 64 PRE; destruct PRE as [ARITH FRAME];
      (eapply nextinv_conj;
       [ apply frame_invset_support
       | copyi_arithmetic_cut D64 U64 N64 SAFE ARITH
       | eapply copyi_frame_vc; [exact ARITH | exact FRAME] ]).
Qed.

Lemma copyi_call_exit_post : forall initial m0 d u n s t,
  true_inv (copyi_call_invset m0 d u n initial ((Addr 0x15b1e2,s)::t)) ->
  copyi_call_post initial m0 d u n s.
Proof. intros. exact H. Qed.
