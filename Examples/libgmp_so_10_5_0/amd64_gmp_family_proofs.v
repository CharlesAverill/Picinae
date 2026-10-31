(* Leaf correctness in the single linked program and fixed invariant family. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_program_transport.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_leaf_transport.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
From Stdlib Require Import NArith.
Import X64Notations.
Open Scope N.

Definition nc_context (sub : bool) (add_ctx sub_ctx : gmp_context) := if sub then sub_ctx else add_ctx.
Definition nc_id (sub : bool) : N := if sub then 2 else 1.
Definition nc_family_inv sub cc ac sc wp := gmp_invs (nc_id sub) cc ac sc wp.
Definition nc_family_exit sub cc ac sc wp := gmp_exits (nc_id sub) cc ac sc wp.

Ltac gmp_agree_at_code :=
  intros pc st tl code LOOK; destruct pc as [|pc];
  repeat first [solve [discriminate LOOK] | solve [split; reflexivity] | destruct pc as [pc|pc|] ].

Lemma family_nc_agree : forall sub cc ac sc wp,
  invariants_agree_on (nc_program sub) (context_nc_inv sub (nc_context sub ac sc))
    (nc_family_inv sub cc ac sc wp) (nc_exit sub) (nc_family_exit sub cc ac sc wp).
Proof. intros [] cc ac sc wp; gmp_agree_at_code. Qed.
Lemma family_copy_agree : forall cc ac sc wp,
  invariants_agree_on libgmp_so_10_5_0___gmpn_copyi_amd64 (context_copy_inv cc)
    (gmp_invs 0 cc ac sc wp) copyi_exit (gmp_exits 0 cc ac sc wp).
Proof. intros cc ac sc wp; gmp_agree_at_code. Qed.

(* Strip program guards before enumerating the fixed address classifier. *)
Definition gmp_class_inv id cc ac sc wp :=
  make_invs id (fun _ _ => Some (0,Nop)) (gmp_family cc ac sc wp).
Lemma gmp_unchecked_pre : forall id cc ac sc wp pc st tl,
  true_inv (get_precondition gmp_linked (gmp_invs id cc ac sc wp)
    (gmp_exits id cc ac sc wp) pc st tl) ->
  true_inv (get_precondition (fun _ _ => Some (0,Nop)) (gmp_class_inv id cc ac sc wp)
    (fun _ => false) pc st tl).
Proof.
  intros id cc ac sc wp pc st tl PRE. unfold get_precondition in PRE.
  destruct (gmp_exits id cc ac sc wp ((Addr pc,st)::tl)); try contradiction.
  destruct (gmp_linked st pc) eqn:CODE; try contradiction.
  unfold gmp_invs,make_invs in PRE. rewrite CODE in PRE. exact PRE.
Qed.
Lemma family_nc_pre : forall sub cc ac sc wp pc st tl,
  true_inv (get_precondition gmp_linked (nc_family_inv sub cc ac sc wp)
    (nc_family_exit sub cc ac sc wp) pc st tl) ->
  true_inv (get_precondition (nc_program sub) (context_nc_inv sub (nc_context sub ac sc))
    (nc_exit sub) pc st nil).
Proof.
  intros sub cc ac sc wp pc st tl PRE.
  assert (EX : nc_family_exit sub cc ac sc wp ((Addr pc,st)::tl)=false).
  { unfold get_precondition in PRE. destruct (nc_family_exit _ _ _ _ _ _) eqn:E;
      [contradiction | reflexivity]. }
  apply gmp_unchecked_pre in PRE.
  destruct sub; destruct_inv 64 PRE; try contradiction; try discriminate EX; exact PRE.
Qed.
Lemma family_copy_pre : forall cc ac sc wp pc st tl,
  true_inv (get_precondition gmp_linked (gmp_invs 0 cc ac sc wp)
    (gmp_exits 0 cc ac sc wp) pc st tl) ->
  true_inv (get_precondition libgmp_so_10_5_0___gmpn_copyi_amd64
    (context_copy_inv cc) copyi_exit pc st nil).
Proof.
  intros cc ac sc wp pc st tl PRE.
  assert (EX : gmp_exits 0 cc ac sc wp ((Addr pc,st)::tl)=false).
  { unfold get_precondition in PRE. destruct (gmp_exits _ _ _ _ _ _) eqn:E;
      [contradiction | reflexivity]. }
  apply gmp_unchecked_pre in PRE.
  destruct_inv 64 PRE; try contradiction; try discriminate EX; exact PRE.
Qed.

Lemma family_nc_head : forall sub cc ac sc wp,
  head_invariant (nc_family_inv sub cc ac sc wp).
Proof. intros sub cc ac sc wp [[a|e] s] t1 t2; reflexivity. Qed.
Lemma family_nc_exit_head : forall sub cc ac sc wp,
  head_exit (nc_family_exit sub cc ac sc wp).
Proof. intros sub cc ac sc wp [[a|e] s] t1 t2; reflexivity. Qed.
Lemma family_copy_head : forall cc ac sc wp, head_invariant (gmp_invs 0 cc ac sc wp).
Proof. intros cc ac sc wp [[a|e] s] t1 t2; reflexivity. Qed.
Lemma family_copy_exit_head : forall cc ac sc wp, head_exit (gmp_exits 0 cc ac sc wp).
Proof. intros cc ac sc wp [[a|e] s] t1 t2; reflexivity. Qed.

Lemma nc_family_cut : forall sub cc ac sc wp pc st tl,
  let c := nc_context sub ac sc in
  models x64typctx st -> 0<call_count c -> call_carry c<=1 -> 8*call_count c<=2^64 ->
  GMPArrays.forward_safe (call_dst c) (call_src1 c) (call_count c) ->
  GMPArrays.forward_safe (call_dst c) (call_src2 c) (call_count c) ->
  true_inv (get_precondition gmp_linked (nc_family_inv sub cc ac sc wp)
    (nc_family_exit sub cc ac sc wp) pc st tl) ->
  nextinv gmp_linked (nc_family_inv sub cc ac sc wp) (nc_family_exit sub cc ac sc wp)
    false ((Addr pc,st)::tl).
Proof.
  intros sub cc ac sc wp pc st tl c MDL POS C B U V PRE.
  eapply nextinv_program_transport with (p:=nc_program sub)
    (I:=context_nc_inv sub c) (xp:=nc_exit sub).
  - apply gmp_extends_nc.
  - apply nc_call_supported.
  - apply family_nc_agree.
  - apply family_nc_head.
  - apply family_nc_exit_head.
  - eapply nc_call_vc; try eassumption. eapply family_nc_pre,PRE.
Qed.
Lemma copy_family_cut : forall cc ac sc wp pc st tl,
  call_dst cc<2^64 -> call_src1 cc<2^64 -> call_count cc<2^64 ->
  GMP64.forward_safe (call_dst cc) (call_src1 cc) (call_count cc) ->
  true_inv (get_precondition gmp_linked (gmp_invs 0 cc ac sc wp)
    (gmp_exits 0 cc ac sc wp) pc st tl) ->
  nextinv gmp_linked (gmp_invs 0 cc ac sc wp) (gmp_exits 0 cc ac sc wp)
    false ((Addr pc,st)::tl).
Proof.
  intros cc ac sc wp pc st tl D64 U64 N64 SAFE PRE.
  eapply nextinv_program_transport with (p:=libgmp_so_10_5_0___gmpn_copyi_amd64)
    (I:=context_copy_inv cc) (xp:=copyi_exit).
  - apply gmp_extends_copyi.
  - apply copyi_call_supported.
  - apply family_copy_agree.
  - apply family_copy_head.
  - apply family_copy_exit_head.
  - eapply copyi_call_vc; try eassumption. eapply family_copy_pre,PRE.
Qed.

Theorem nc_family_correctness_from : forall sub cc ac sc wp a t st' x',
  let c := nc_context sub ac sc in
  startof t (x',st')=(Addr (nc_address sub a),call_initial c) ->
  (a=0x1284e0 \/ a=0x128500) -> models x64typctx (call_initial c) ->
  true_inv (context_nc_inv sub c ((Addr (nc_address sub a),call_initial c)::nil)) ->
  0<call_count c -> call_carry c<=1 -> 8*call_count c<=2^64 ->
  GMPArrays.forward_safe (call_dst c) (call_src1 c) (call_count c) ->
  GMPArrays.forward_safe (call_dst c) (call_src2 c) (call_count c) ->
  satisfies_all gmp_linked (nc_family_inv sub cc ac sc wp) (nc_family_exit sub cc ac sc wp)
    ((x',st')::t).
Proof.
  intros sub cc ac sc wp a t st' x' c ENTRY START MDL INITIAL POS C B U V.
  apply prove_invs.
  - simpl. rewrite ENTRY. destruct START as [A|A]; subst a; destruct sub;
      x64_step; exact INITIAL.
  - intros t1 a1 s1 t2 UT SPL PRE.
    eapply models_at_invariant.
    + exact MDL.
    + apply gmp_linked_welltyped.
    + rewrite <-(startof_prefix _ _ _ _ _ SPL). exact ENTRY.
    + intro CURRENT. eapply nc_family_cut; eassumption.
Qed.

Lemma context_nc_initial : forall sub c,
  call_initial c R_RDI=call_dst c -> call_initial c R_RSI=call_src1 c ->
  call_initial c R_RDX=call_src2 c -> call_initial c R_RCX=call_count c ->
  call_initial c R_R8=call_carry c ->
  true_inv (context_nc_inv sub c ((Addr (nc_address sub 0x1284e0),call_initial c)::nil)).
Proof.
  intros sub c D U V N C. destruct sub;
    (split; [repeat split; try assumption; reflexivity |
      split; [unfold leaf_abi; repeat split; reflexivity | apply outside_output_refl] ]).
Qed.

(* __gmpn_add_nc precondition *)
(* __gmpn_sub_nc precondition *)
Theorem nc_family_correctness : forall sub cc ac sc wp t st' x',
  let c := nc_context sub ac sc in
  startof t (x',st')=(Addr (nc_address sub 0x1284e0),call_initial c) ->
  models x64typctx (call_initial c) ->
  call_initial c R_RDI=call_dst c -> call_initial c R_RSI=call_src1 c ->
  call_initial c R_RDX=call_src2 c -> call_initial c R_RCX=call_count c ->
  call_initial c R_R8=call_carry c ->
  0<call_count c -> call_carry c<=1 -> 8*call_count c<=2^64 ->
  GMPArrays.forward_safe (call_dst c) (call_src1 c) (call_count c) ->
  GMPArrays.forward_safe (call_dst c) (call_src2 c) (call_count c) ->
  satisfies_all gmp_linked (nc_family_inv sub cc ac sc wp) (nc_family_exit sub cc ac sc wp)
    ((x',st')::t).
Proof.
  intros. eapply nc_family_correctness_from; try eassumption.
  - left. reflexivity.
  - apply context_nc_initial; assumption.
Qed.

(* __gmpn_copyi precondition *)
Theorem copy_family_correctness : forall cc ac sc wp t st' x',
  startof t (x',st')=(Addr 0x15b186,call_initial cc) -> models x64typctx (call_initial cc) ->
  call_initial cc R_RDI=call_dst cc -> call_initial cc R_RSI=call_src1 cc ->
  call_initial cc R_RDX=call_count cc ->
  GMP64.forward_safe (call_dst cc) (call_src1 cc) (call_count cc) ->
  satisfies_all gmp_linked (gmp_invs 0 cc ac sc wp) (gmp_exits 0 cc ac sc wp) ((x',st')::t).
Proof.
  intros cc ac sc wp t st' x' ENTRY MDL D U N SAFE.
  assert (D64 : call_dst cc<2^64) by (pose proof (models_var R_RDI MDL) as H; rewrite D in H; exact H).
  assert (U64 : call_src1 cc<2^64) by (pose proof (models_var R_RSI MDL) as H; rewrite U in H; exact H).
  assert (N64 : call_count cc<2^64) by (pose proof (models_var R_RDX MDL) as H; rewrite N in H; exact H).
  apply prove_invs.
  - simpl. rewrite ENTRY. x64_step.
    split; [repeat split; try assumption; reflexivity |
      split; [unfold leaf_abi; repeat split; reflexivity | apply outside_output_refl] ].
  - intros. eapply copy_family_cut; eassumption.
Qed.
