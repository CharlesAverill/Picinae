(* Derive leaf call premises from the wrapper's alias and stack contract. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma forward_safe_disjoint64 : forall d p n,
  array_separate d p n -> forward_safe d p n.
Proof.
  intros d p n SEP k j K. unfold GMPArrayParams.w,GMPArrayParams.bytes.
  pose proof (noverlap_index_index 64 p (8*n) d (8*n) (8*k) (8*j) 0 (8*k)
    (noverlap_symmetry _ _ _ _ _ SEP) ltac:(nia) ltac:(nia)) as H.
  rewrite N.add_0_r in H. exact H.
Qed.
Lemma forward_safe_same64 : forall p n,
  8*n<=2^64 -> forward_safe p p n.
Proof.
  intros p n B k j K. unfold GMPArrayParams.w,GMPArrayParams.bytes.
  apply noverlap_symmetry,noverlap_adjacent64. nia.
Qed.
Lemma forward_safe_chunks64 : forall d p n k q,
  exact_or_separate d p n -> 8*n<=2^64 -> k+q<=n ->
  forward_safe (limb_ptr d k) (limb_ptr p k) q.
Proof.
  intros d p n k q ALIAS B K. unfold forward_safe,GMPArrayParams.w,GMPArrayParams.bytes.
  intros i j IJ. unfold limb_ptr.
  rewrite <-noverlap_mod_idemp_l, N.Div0.add_mod_idemp_l, noverlap_mod_idemp_l.
  apply noverlap_symmetry. rewrite noverlap_mod_idemp_l. apply noverlap_symmetry.
  destruct ALIAS as [EQ|SEP].
  - subst p. replace (d+8*k+8*i) with (d+8*k+8*i) by reflexivity.
    apply noverlap_symmetry,noverlap_adjacent64. nia.
  - replace (p+8*k+8*i) with (p+8*(k+i)) by nia.
    eapply noverlap_index_index; [apply noverlap_symmetry,SEP | nia | nia].
Qed.

Lemma wrapper_operand_stack : forall r p k q,
  wrapper_pre r ->
  (p=wrapper_sum r \/ p=wrapper_diff r \/ p=wrapper_u r \/ p=wrapper_v r) ->
  k+q<=wrapper_n r ->
  ~overlap 64 (limb_ptr p k) (8*q) (wrapper_stack r) 0x5b0.
Proof.
  intros r p k q (MDL & BN & B & STACK & DISJ & ALIAS & SEP) PTR K.
  unfold limb_ptr. apply noverlap_mod_idemp_l.
  eapply noverlap_index_l; [exact (proj2 (SEP p PTR)) | nia].
Qed.
Lemma wrapper_call_cell : forall r,
  wrapper_pre r -> wrapper_frame r ⊖ 8=wrapper_stack r.
Proof.
  intros r (MDL & BN & B & STACK & REST).
  pose proof (models_var R_RSP MDL) as SPB. change (r R_RSP<2^64) in SPB.
  unfold wrapper_frame,wrapper_stack. rewrite msub_sub by lia.
  rewrite N.mod_small by lia. lia.
Qed.
Lemma wrapper_operand_call_cell : forall r p k q,
  wrapper_pre r ->
  (p=wrapper_sum r \/ p=wrapper_diff r \/ p=wrapper_u r \/ p=wrapper_v r) ->
  k+q<=wrapper_n r ->
  ~overlap 64 (limb_ptr p k) (8*q) (wrapper_frame r ⊖ 8) 8.
Proof.
  intros r p k q PRE PTR K. rewrite wrapper_call_cell by exact PRE.
  replace (wrapper_stack r) with (wrapper_stack r+0) at 1 by lia.
  eapply noverlap_index_r; [eapply wrapper_operand_stack; eassumption | lia].
Qed.

(* __gmpn_add_nc precondition *)
(* __gmpn_sub_nc precondition *)
Definition wrapper_nc_call_ready (s : store) :=
  0<s R_RCX /\ s R_R8<=1 /\ 8*s R_RCX<=2^64 /\
  forward_safe (s R_RDI) (s R_RSI) (s R_RCX) /\
  forward_safe (s R_RDI) (s R_RDX) (s R_RCX) /\
  ~overlap 64 (s R_RSP ⊖ 8) 8 (s R_RDI) (8*s R_RCX) /\
  ~overlap 64 (s R_RSI) (8*s R_RCX) (s R_RSP ⊖ 8) 8 /\
  ~overlap 64 (s R_RDX) (8*s R_RCX) (s R_RSP ⊖ 8) 8.
Lemma wrapper_nc_operands_ready : forall r s d k cin,
  wrapper_pre r -> k<wrapper_n r -> cin<=1 ->
  (d=wrapper_sum r \/ d=wrapper_diff r) ->
  s R_RDI=limb_ptr d k -> s R_RSI=limb_ptr (wrapper_u r) k ->
  s R_RDX=limb_ptr (wrapper_v r) k -> s R_RCX=chunk_size (wrapper_n r) k ->
  s R_R8=cin -> s R_RSP=wrapper_frame r -> wrapper_nc_call_ready s.
Proof.
  intros r s d k cin PRE K C D DI SI DX CX CI SP. pose proof PRE as ROOT.
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  destruct PRE as (MDL & BN & B & STACK & DISJ & ALIAS & SEP).
  unfold wrapper_nc_call_ready. rewrite DI,SI,DX,CX,CI,SP.
  repeat (split; [assumption | ]).
  split; [nia | ]. split.
  - apply forward_safe_chunks64 with (n:=wrapper_n r); [apply ALIAS; tauto | exact B | exact END].
  - split.
    + apply forward_safe_chunks64 with (n:=wrapper_n r); [apply ALIAS; tauto | exact B | exact END].
    + split.
      * apply noverlap_symmetry. eapply wrapper_operand_call_cell; [exact ROOT | tauto | exact END].
      * split; eapply wrapper_operand_call_cell; [exact ROOT | tauto | exact END |
          exact ROOT | tauto | exact END].
Qed.

Lemma wrapper_scratch_disjoint : forall r p k q,
  wrapper_pre r ->
  (p=wrapper_u r \/ p=wrapper_v r) -> k+q<=wrapper_n r -> q<=170 ->
  array_separate (wrapper_frame r+32) (limb_ptr p k) q.
Proof.
  intros r p k q PRE PTR K Q. unfold array_separate. apply noverlap_symmetry.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  replace (wrapper_frame r+32) with (wrapper_stack r+40) by (unfold wrapper_frame,wrapper_stack; lia).
  eapply noverlap_index_r; [eapply wrapper_operand_stack; [exact PRE | tauto | exact K] | nia].
Qed.
Lemma wrapper_nc_scratch_ready : forall r s k cin,
  wrapper_pre r -> k<wrapper_n r -> cin<=1 ->
  s R_RDI=wrapper_frame r+32 -> s R_RSI=limb_ptr (wrapper_u r) k ->
  s R_RDX=limb_ptr (wrapper_v r) k -> s R_RCX=chunk_size (wrapper_n r) k ->
  s R_R8=cin -> s R_RSP=wrapper_frame r -> wrapper_nc_call_ready s.
Proof.
  intros r s k cin PRE K C DI SI DX CX CI SP.
  pose proof (chunk_size_bounds (wrapper_n r) k K) as (QP & QB & END).
  unfold wrapper_nc_call_ready. rewrite DI,SI,DX,CX,CI,SP.
  split; [exact QP | ]. split; [exact C | ]. split; [nia | ].
  split; [apply forward_safe_disjoint64; eapply wrapper_scratch_disjoint; [exact PRE | tauto | exact END | exact QB] | ].
  split; [apply forward_safe_disjoint64; eapply wrapper_scratch_disjoint; [exact PRE | tauto | exact END | exact QB] | ].
  split.
  - rewrite wrapper_call_cell by exact PRE.
    assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
    replace (wrapper_frame r+32) with (wrapper_stack r+40) by (unfold wrapper_frame,wrapper_stack; lia).
    replace (wrapper_stack r+40) with (wrapper_stack r+8+32) by lia.
    eapply noverlap_index_r with (a2:=wrapper_stack r+8) (index:=32) (len2:=32+8*chunk_size (wrapper_n r) k).
    + apply noverlap_adjacent64. nia.
    + nia.
  - split; eapply wrapper_operand_call_cell; [exact PRE | tauto | exact END | exact PRE | tauto | exact END].
Qed.
