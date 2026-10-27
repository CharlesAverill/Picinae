(* Call composition in the linked program, including the actual AMD64 RET. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family_proofs.
From Stdlib Require Import NArith.
Import X64Notations.
Open Scope N.

Definition gmp_class_exit id cc ac sc wp :=
  make_exits id (fun _ _ => Some (0,Nop)) (gmp_family cc ac sc wp).
Lemma gmp_unchecked_post : forall id cc ac sc wp pc st tl,
  true_inv (get_postcondition gmp_linked (gmp_invs id cc ac sc wp)
    (gmp_exits id cc ac sc wp) pc st tl) ->
  true_inv (get_postcondition (fun _ _ => Some (0,Nop)) (gmp_class_inv id cc ac sc wp)
    (gmp_class_exit id cc ac sc wp) pc st tl).
Proof.
  intros id cc ac sc wp pc st tl PRE. unfold get_postcondition in PRE.
  destruct (gmp_linked st pc) eqn:CODE.
  - unfold gmp_exits,make_exits,gmp_invs,make_invs in PRE.
    rewrite CODE in PRE. exact PRE.
  - unfold gmp_exits,make_exits in PRE. rewrite CODE in PRE. contradiction.
Qed.

Definition returned_initial c :=
  (call_initial c)[R_RSP:=8 ⊕ call_initial c R_RSP].
Definition ret_store (s : store) ra := s[R_RIP:=ra][R_RSP:=8 ⊕ s R_RSP].
(* __gmpn_add_nc postcondition *)
(* __gmpn_sub_nc postcondition *)
Definition nc_resume_post sub c s :=
  nc_post sub (call_memory c) (call_dst c) (call_src1 c) (call_src2 c)
    (call_count c) (call_carry c) s /\
  leaf_frame (returned_initial c) (call_memory c) (call_dst c) (call_count c) s.

Lemma nc_ret_post : forall sub c s ra,
  nc_call_post sub (call_initial c) (call_memory c) (call_dst c) (call_src1 c)
    (call_src2 c) (call_count c) (call_carry c) s ->
  nc_resume_post sub c (ret_store s ra).
Proof.
  intros sub c s ra [POST [ABI OUT]]. split.
  - unfold nc_post in POST |- *. unfold ret_store. nc_updates. exact POST.
  - unfold leaf_frame,leaf_abi,returned_initial,ret_store in *.
    nc_updates. destruct ABI as [SP ABI]. rewrite SP.
    split; [repeat split; try reflexivity; tauto | exact OUT].
Qed.

Ltac nc_finish_return sub c ra RET SEP CONT :=
  let pc := fresh "pc" in let after := fresh "after" in let tr := fresh "tr" in
  let ENTRY := fresh "ENTRY" in let XP := fresh "XP" in let UT := fresh "UT" in
  let PRE := fresh "POST" in let SP := fresh "SP" in let CELL := fresh "CELL" in
  intros pc after tr ENTRY XP UT PRE;
  apply gmp_unchecked_post in PRE; destruct_inv 64 PRE;
  change (nc_call_post sub (call_initial c) (call_memory c) (call_dst c) (call_src1 c)
    (call_src2 c) (call_count c) (call_carry c) after) in PRE;
  pose proof (leaf_frame_return_cell _ _ _ _ after (proj2 PRE) SEP) as [SP CELL];
  rewrite RET in CELL;
  x64_step;
  rewrite <-SP; rewrite ?CELL;
  eapply CONT;
  change (nc_resume_post sub c (ret_store after ra));
  apply nc_ret_post; exact PRE.

Theorem nc_perform_call : forall sub cc ac sc c wp ra t,
  models x64typctx (call_initial c) ->
  call_initial c R_RDI=call_dst c -> call_initial c R_RSI=call_src1 c ->
  call_initial c R_RDX=call_src2 c -> call_initial c R_RCX=call_count c ->
  call_initial c R_R8=call_carry c ->
  0<call_count c -> call_carry c<=1 -> 8*call_count c<=2^64 ->
  GMPArrays.forward_safe (call_dst c) (call_src1 c) (call_count c) ->
  GMPArrays.forward_safe (call_dst c) (call_src2 c) (call_count c) ->
  (call_memory c) Ⓠ[call_initial c R_RSP]=ra ->
  ~overlap 64 (call_initial c R_RSP) 8 (call_dst c) (8*call_count c) ->
  (forall after tr, nc_resume_post sub c after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
      true ((Addr ra,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
    true ((Addr (nc_address sub 0x1284e0),call_initial c)::t).
Proof.
  intros sub cc ac sc c wp ra t MDL D U V N C POS CB B SU SV RET SEP CONT.
  destruct sub.
  - eapply (perform_call 2) with (g:=gmp_family cc ac c wp).
    + reflexivity.
    + intros t0 [x0 s0] ENTRY. eapply (nc_family_correctness true cc ac c wp); eassumption.
    + apply gmp_same_invset_family.
    + nc_finish_return true c ra RET SEP CONT.
  - eapply (perform_call 1) with (g:=gmp_family cc c sc wp).
    + reflexivity.
    + intros t0 [x0 s0] ENTRY. eapply (nc_family_correctness false cc c sc wp); eassumption.
    + apply gmp_same_invset_family.
    + nc_finish_return false c ra RET SEP CONT.
Qed.

Definition call_enter (s : store) (ra : N) :=
  s[R_RSP:=s R_RSP ⊖ 8][V_MEM64:=(s V_MEM64)[Ⓠs R_RSP ⊖ 8:=ra]].
Definition nc_after_call (s : store) ra : gmp_context :=
  {| call_initial:=call_enter s ra; call_dst:=s R_RDI; call_src1:=s R_RSI;
     call_src2:=s R_RDX; call_count:=s R_RCX; call_carry:=s R_R8 |}.
Lemma call_enter_return_cell : forall s ra,
  ra<2^64 -> (call_enter s ra V_MEM64) Ⓠ[call_enter s ra R_RSP]=ra.
Proof.
  intros s ra B. unfold call_enter. nc_updates.
  rewrite getmem_setmem by (vm_compute; easy).
  apply N.mod_small,B.
Qed.
Definition nc_call_site (sub : bool) site ra :=
  if sub then (site=0x15c41b /\ ra=0x15c420) \/
              (site=0x15c4b2 /\ ra=0x15c4b7) \/ (site=0x15c592 /\ ra=0x15c597)
         else (site=0x15c3ea /\ ra=0x15c3ef) \/
              (site=0x15c4e3 /\ ra=0x15c4e8) \/ (site=0x15c563 /\ ra=0x15c568).

Ltac nc_prefix_finish sub cc ac sc wp s ra RA MDL :=
  x64_step; x64_step; rewrite <-RA;
  eapply models_after_steps; [exact MDL | apply gmp_linked_welltyped | ];
  let CURRENT := fresh "CURRENT" in intro CURRENT;
  eapply (nc_perform_call sub cc ac sc (nc_after_call s ra) wp ra);
  try eassumption;
  try solve [cbn [nc_after_call]; unfold call_enter; nc_updates; reflexivity];
  try solve [cbn [nc_after_call]; unfold call_enter; nc_updates; assumption];
  apply call_enter_return_cell; rewrite RA; reflexivity.

(* Every arithmetic CALL site, including its PLT jump and the callee RET. *)
Lemma nc_wrapper_call : forall sub site ra cc ac sc wp s t,
  nc_call_site sub site ra -> models x64typctx s ->
  0<s R_RCX -> s R_R8<=1 -> 8*s R_RCX<=2^64 ->
  GMPArrays.forward_safe (s R_RDI) (s R_RSI) (s R_RCX) ->
  GMPArrays.forward_safe (s R_RDI) (s R_RDX) (s R_RCX) ->
  ~overlap 64 (s R_RSP ⊖ 8) 8 (s R_RDI) (8*s R_RCX) ->
  (forall after tr, nc_resume_post sub (nc_after_call s ra) after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
      true ((Addr ra,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
    false ((Addr site,s)::t).
Proof.
  intros sub site ra cc ac sc wp s t SITE MDL POS C B U V SEP CONT.
  destruct sub.
  - cbn [nc_call_site] in SITE. destruct SITE as [[A RA]|[[A RA]|[A RA]]]; subst site;
      nc_prefix_finish true cc ac sc wp s ra RA MDL.
  - cbn [nc_call_site] in SITE. destruct SITE as [[A RA]|[[A RA]|[A RA]]]; subst site;
      nc_prefix_finish false cc ac sc wp s ra RA MDL.
Qed.

(* __gmpn_copyi postcondition *)
Definition copy_resume_post c s :=
  s V_MEM64=GMP64.copied (call_memory c) (call_dst c) (call_src1 c) (call_count c) /\
  leaf_frame (returned_initial c) (call_memory c) (call_dst c) (call_count c) s.
Lemma copy_ret_post : forall c s ra,
  copyi_call_post (call_initial c) (call_memory c) (call_dst c) (call_src1 c) (call_count c) s ->
  copy_resume_post c (ret_store s ra).
Proof.
  intros c s ra [MEM [ABI OUT]]. split.
  - unfold ret_store. nc_updates. exact MEM.
  - unfold leaf_frame,leaf_abi,returned_initial,ret_store in *.
    nc_updates. destruct ABI as [SP ABI]. rewrite SP.
    split; [repeat split; try reflexivity; tauto | exact OUT].
Qed.

Theorem copy_perform_call : forall cc ac sc c wp ra t,
  models x64typctx (call_initial c) ->
  call_initial c R_RDI=call_dst c -> call_initial c R_RSI=call_src1 c ->
  call_initial c R_RDX=call_count c ->
  GMP64.forward_safe (call_dst c) (call_src1 c) (call_count c) ->
  (call_memory c) Ⓠ[call_initial c R_RSP]=ra ->
  ~overlap 64 (call_initial c R_RSP) 8 (call_dst c) (8*call_count c) ->
  (forall after tr, copy_resume_post c after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
      true ((Addr ra,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
    true ((Addr 0x15b186,call_initial c)::t).
Proof.
  intros cc ac sc c wp ra t MDL D U N SAFE RET SEP CONT.
  eapply (perform_call 0) with (g:=gmp_family c ac sc wp).
  - reflexivity.
  - intros t0 [x0 s0] ENTRY. eapply (copy_family_correctness c ac sc wp); eassumption.
  - apply gmp_same_invset_family.
  - intros pc after tr ENTRY XP UT PRE.
    apply gmp_unchecked_post in PRE. destruct_inv 64 PRE.
    change (copyi_call_post (call_initial c) (call_memory c) (call_dst c)
      (call_src1 c) (call_count c) after) in PRE.
    pose proof (leaf_frame_return_cell _ _ _ _ after (proj2 PRE) SEP) as [SP CELL].
    rewrite RET in CELL. x64_step. rewrite <-SP,CELL.
    eapply CONT. change (copy_resume_post c (ret_store after ra)).
    apply copy_ret_post,PRE.
Qed.

Definition copy_after_call (s : store) ra : gmp_context :=
  {| call_initial:=call_enter s ra; call_dst:=s R_RDI; call_src1:=s R_RSI;
     call_src2:=0; call_count:=s R_RDX; call_carry:=0 |}.
Lemma copy_wrapper_call : forall cc ac sc wp s t,
  models x64typctx s -> GMP64.forward_safe (s R_RDI) (s R_RSI) (s R_RDX) ->
  ~overlap 64 (s R_RSP ⊖ 8) 8 (s R_RDI) (8*s R_RDX) ->
  (forall after tr, copy_resume_post (copy_after_call s 0x15c5b1) after ->
    nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
      true ((Addr 0x15c5b1,after)::tr)) ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc wp) (gmp_exits 3 cc ac sc wp)
    false ((Addr 0x15c5ac,s)::t).
Proof.
  intros cc ac sc wp s t MDL SAFE SEP CONT.
  x64_step. x64_step.
  eapply models_after_steps; [exact MDL | apply gmp_linked_welltyped | ]. intro CURRENT.
  eapply (copy_perform_call cc ac sc (copy_after_call s 0x15c5b1) wp 0x15c5b1);
    try eassumption;
    try solve [cbn [copy_after_call]; unfold call_enter; nc_updates; reflexivity];
    try solve [cbn [copy_after_call]; unfold call_enter; nc_updates; assumption].
  apply call_enter_return_cell. reflexivity.
Qed.

(* The callee snapshot includes CALL's pushed return address. These lemmas
   recover the pre-CALL operand values when that write is disjoint. *)
Lemma call_enter_value : forall s ra p n,
  ~overlap 64 p (8*n) (s R_RSP ⊖ 8) 8 ->
  GMPArrays.value (call_enter s ra V_MEM64) p n=GMPArrays.value (s V_MEM64) p n.
Proof.
  intros s ra p n SEP. unfold call_enter. nc_updates.
  unfold GMPArrays.value,GMPArrayParams.w,GMPArrayParams.bytes.
  apply getmem_noverlap,SEP.
Qed.
Lemma nc_resume_original_inputs : forall sub s ra after,
  ~overlap 64 (s R_RSI) (8*s R_RCX) (s R_RSP ⊖ 8) 8 ->
  ~overlap 64 (s R_RDX) (8*s R_RCX) (s R_RSP ⊖ 8) 8 ->
  nc_resume_post sub (nc_after_call s ra) after ->
  nc_post sub (s V_MEM64) (s R_RDI) (s R_RSI) (s R_RDX) (s R_RCX) (s R_R8) after.
Proof.
  intros sub s ra after U V [POST FRAME].
  change (nc_post sub (call_enter s ra V_MEM64) (s R_RDI) (s R_RSI) (s R_RDX)
    (s R_RCX) (s R_R8) after) in POST.
  unfold nc_post in POST |- *.
  rewrite (call_enter_value s ra _ _ U), (call_enter_value s ra _ _ V) in POST.
  exact POST.
Qed.

Lemma copy_copied_value : forall m d u n,
  8*n<=2^64 -> GMP64.value (GMP64.copied m d u n) d n=GMP64.value m u n.
Proof.
  intros m d u n B. unfold GMP64.value,GMP64.copied,GMP64Params.w,GMP64Params.bytes.
  rewrite getmem_setmem by exact B.
  apply N.mod_small,getmem_bound.
Qed.
Lemma copy_resume_original_input : forall s ra after,
  8*s R_RDX<=2^64 ->
  ~overlap 64 (s R_RSI) (8*s R_RDX) (s R_RSP ⊖ 8) 8 ->
  copy_resume_post (copy_after_call s ra) after ->
  GMP64.value (after V_MEM64) (s R_RDI) (s R_RDX)=
    GMP64.value (s V_MEM64) (s R_RSI) (s R_RDX).
Proof.
  intros s ra after B SEP [MEM FRAME].
  change (after V_MEM64=GMP64.copied (call_enter s ra V_MEM64)
    (s R_RDI) (s R_RSI) (s R_RDX)) in MEM.
  rewrite MEM,copy_copied_value by exact B.
  apply call_enter_value,SEP.
Qed.

Lemma leaf_abi_trans : forall s0 s1 s2,
  leaf_abi s0 s1 -> leaf_abi s1 s2 -> leaf_abi s0 s2.
Proof. unfold leaf_abi; intros; intuition congruence. Qed.
Lemma returned_initial_abi : forall s ra,
  models x64typctx s -> leaf_abi s (returned_initial (nc_after_call s ra)).
Proof.
  intros s ra MDL.
  pose proof (models_var R_RSP MDL) as B. change (s R_RSP<2^64) in B.
  unfold leaf_abi,returned_initial,nc_after_call,call_enter. cbn [call_initial].
  nc_updates. psimpl. repeat split; try reflexivity.
Qed.
Lemma nc_resume_caller_frame : forall sub s ra after,
  models x64typctx s -> nc_resume_post sub (nc_after_call s ra) after ->
  leaf_frame s (call_enter s ra V_MEM64) (s R_RDI) (s R_RCX) after.
Proof.
  intros sub s ra after MDL [POST [ABI OUT]]. split; [ | exact OUT].
  eapply leaf_abi_trans; [apply returned_initial_abi,MDL | exact ABI].
Qed.
Lemma copy_resume_caller_frame : forall s ra after,
  models x64typctx s -> copy_resume_post (copy_after_call s ra) after ->
  leaf_frame s (call_enter s ra V_MEM64) (s R_RDI) (s R_RDX) after.
Proof.
  intros s ra after MDL [MEM [ABI OUT]]. split; [ | exact OUT].
  eapply leaf_abi_trans; [apply returned_initial_abi,MDL | exact ABI].
Qed.
