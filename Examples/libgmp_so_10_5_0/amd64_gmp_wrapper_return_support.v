(* Memory and arithmetic composition across CALL's push and a leaf result. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_call_conditions.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma value_limb_ptr : forall m p k n, value m (limb_ptr p k) n=value m (p+8*k) n.
Proof. intros. apply getmem_mod_l. Qed.
Lemma wrapper_stack_call_cell : forall r offset size,
  wrapper_pre r -> offset+size<=0x5a8 ->
  ~overlap 64 (wrapper_frame r+offset) size (wrapper_stack r) 8.
Proof.
  intros r offset size PRE B.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  replace (wrapper_frame r+offset) with (wrapper_stack r+8+offset)
    by (unfold wrapper_frame,wrapper_stack; lia).
  apply noverlap_symmetry. eapply noverlap_index_r.
  - apply noverlap_adjacent64. instantiate (1:=offset+size). lia.
  - lia.
Qed.
Lemma wrapper_stack_operand : forall r offset size d k q,
  wrapper_pre r -> offset+size<=0x5a8 -> k+q<=wrapper_n r ->
  (d=wrapper_sum r \/ d=wrapper_diff r) ->
  ~overlap 64 (wrapper_frame r+offset) size (limb_ptr d k) (8*q).
Proof.
  intros r offset size d k q PRE OFF K D.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  replace (wrapper_frame r+offset) with (wrapper_stack r+(8+offset))
    by (unfold wrapper_frame,wrapper_stack; lia).
  eapply noverlap_index_l; [apply noverlap_symmetry; eapply wrapper_operand_stack; [exact PRE | tauto | exact K] | lia].
Qed.
Definition wrapper_call_frame r before after d bytes :=
  forall p len, ~overlap 64 p len d bytes -> ~overlap 64 p len (wrapper_stack r) 8 ->
    getmem 64 LittleE len after p=getmem 64 LittleE len before p.
Lemma nc_resume_frame : forall sub r caller ra after,
  wrapper_pre r -> models x64typctx caller -> caller R_RSP=wrapper_frame r ->
  nc_resume_post sub (nc_after_call caller ra) after ->
  leaf_abi caller after /\ wrapper_call_frame r (caller V_MEM64) (after V_MEM64)
    (caller R_RDI) (8*caller R_RCX).
Proof.
  intros sub r caller ra after PRE MDL SP POST.
  pose proof (nc_resume_caller_frame sub caller ra after MDL POST) as [ABI OUT].
  split; [exact ABI | ]. intros p len DST CELL. rewrite OUT by exact DST.
  unfold call_enter. nc_updates. rewrite SP,wrapper_call_cell by exact PRE.
  apply getmem_noverlap,CELL.
Qed.
Lemma wrapper_frame_saved : forall r before after d bytes,
  wrapper_pre r -> wrapper_call_frame r before after d bytes -> wrapper_saved r before ->
  (forall offset, offset=0x578 \/ offset=0x580 \/ offset=0x588 \/
    offset=0x590 \/ offset=0x598 \/ offset=0x5a0 ->
    ~overlap 64 (wrapper_frame r+offset) 8 d bytes) -> wrapper_saved r after.
Proof.
  intros r before after d bytes PRE FRAME SAVED SEP. unfold wrapper_saved in *.
  rewrite (FRAME (wrapper_frame r+0x578) 8), (FRAME (wrapper_frame r+0x580) 8),
    (FRAME (wrapper_frame r+0x588) 8), (FRAME (wrapper_frame r+0x590) 8),
    (FRAME (wrapper_frame r+0x598) 8), (FRAME (wrapper_frame r+0x5a0) 8);
    try solve [apply SEP; tauto]; try solve [eapply wrapper_stack_call_cell; [exact PRE | lia]].
  exact SAVED.
Qed.
Lemma wrapper_frame_output : forall r before after d k q,
  wrapper_pre r -> k+q<=wrapper_n r -> (d=wrapper_sum r \/ d=wrapper_diff r) ->
  wrapper_call_frame r before after (limb_ptr d k) (8*q) ->
  wrapper_memory_frame r before -> wrapper_memory_frame r after.
Proof.
  intros r before after d k q PRE K D OUT FRAME p len SUM DIFF STACK.
  transitivity (getmem 64 LittleE len before p); [apply OUT | apply FRAME; assumption].
  - unfold limb_ptr. apply noverlap_symmetry. rewrite noverlap_mod_idemp_l. apply noverlap_symmetry.
    destruct D as [-> | ->]; eapply noverlap_index_r; [exact SUM | | exact DIFF | ]; nia.
  - replace (wrapper_stack r) with (wrapper_stack r+0) at 1 by lia.
    eapply noverlap_index_r; [exact STACK | lia].
Qed.
Lemma wrapper_common_result : forall r caller after d k q,
  wrapper_pre r -> k+q<=wrapper_n r -> (d=wrapper_sum r \/ d=wrapper_diff r) ->
  wrapper_common r caller -> leaf_abi caller after ->
  wrapper_call_frame r (caller V_MEM64) (after V_MEM64) (limb_ptr d k) (8*q) ->
  wrapper_common r after.
Proof.
  intros r caller after d k q PRE K D (SP & LEN & SAVED & FRAME) ABI OUT.
  unfold leaf_abi in ABI. destruct ABI as (SP' & BX & BP & LEN' & REST).
  unfold wrapper_common. split; [congruence | ]. split; [congruence | ]. split.
  - eapply wrapper_frame_saved; [exact PRE | exact OUT | exact SAVED | ].
    intros offset OFF. eapply wrapper_stack_operand; [exact PRE | destruct OFF as [-> | [-> | [-> | [-> | [-> | ->]]]]]; lia | exact K | exact D].
  - eapply wrapper_frame_output; eassumption.
Qed.

Definition wrapper_prefix sub r m d k c :=
  nc_equation sub (value m d k) (value (r V_MEM64) (wrapper_u r) k)
    (value (r V_MEM64) (wrapper_v r) k) 0 c k.
Lemma wrapper_chunk_result : forall sub r caller ra after d k q,
  wrapper_pre r -> models x64typctx caller -> k+q<=wrapper_n r ->
  (d=wrapper_sum r \/ d=wrapper_diff r) ->
  caller R_RSP=wrapper_frame r -> caller R_RDI=limb_ptr d k ->
  caller R_RSI=limb_ptr (wrapper_u r) k -> caller R_RDX=limb_ptr (wrapper_v r) k ->
  caller R_RCX=q -> wrapper_unread r (caller V_MEM64) k ->
  wrapper_prefix sub r (caller V_MEM64) d k (caller R_R8) ->
  nc_resume_post sub (nc_after_call caller ra) after ->
  after R_RAX<=1 /\ wrapper_prefix sub r (after V_MEM64) d (k+q) (after R_RAX).
Proof.
  intros sub r caller ra after d k q PRE MDL K D SP DI SI DX CX UN PREFIX POST.
  assert (SU:~overlap 64 (caller R_RSI) (8*caller R_RCX) (caller R_RSP ⊖ 8) 8).
  { rewrite SI,CX,SP. eapply wrapper_operand_call_cell; [exact PRE | tauto | exact K]. }
  assert (SV:~overlap 64 (caller R_RDX) (8*caller R_RCX) (caller R_RSP ⊖ 8) 8).
  { rewrite DX,CX,SP. eapply wrapper_operand_call_cell; [exact PRE | tauto | exact K]. }
  pose proof (nc_resume_original_inputs sub caller ra after SU SV POST) as [BIT EQ].
  rewrite DI,SI,DX,CX,!value_limb_ptr in EQ.
  pose proof (unread_chunk _ _ _ _ _ _ _ K UN) as [UV VV]. rewrite UV,VV in EQ.
  pose proof (nc_resume_frame sub r caller ra after PRE MDL SP POST) as [ABI FRAME].
  rewrite DI,CX in FRAME.
  split; [exact BIT | ]. unfold wrapper_prefix in PREFIX |- *.
  eapply nc_chunk_append; [exact PREFIX | exact EQ | ].
  apply FRAME.
  - unfold limb_ptr. apply noverlap_symmetry. rewrite noverlap_mod_idemp_l. apply noverlap_symmetry.
    apply noverlap_adjacent64. pose proof (proj1 (proj2 (proj2 PRE))) as B. nia.
  - pose proof (wrapper_operand_call_cell r d 0 k PRE ltac:(tauto) ltac:(lia)) as H.
    unfold limb_ptr in H. rewrite N.mul_0_r,N.add_0_r in H.
    rewrite noverlap_mod_idemp_l in H. rewrite wrapper_call_cell in H by exact PRE. exact H.
Qed.

Lemma wrapper_frame_operand_value : forall r before after d bytes p i j,
  wrapper_pre r -> i+j<=wrapper_n r ->
  (p=wrapper_sum r \/ p=wrapper_diff r \/ p=wrapper_u r \/ p=wrapper_v r) ->
  wrapper_call_frame r before after d bytes ->
  ~overlap 64 (p+8*i) (8*j) d bytes ->
  value after (p+8*i) j=value before (p+8*i) j.
Proof.
  intros r before after d bytes p i j PRE B PTR FRAME SEP. apply FRAME; [exact SEP | ].
  pose proof (wrapper_operand_call_cell r p i j PRE PTR B) as H.
  unfold limb_ptr in H. rewrite noverlap_mod_idemp_l,wrapper_call_cell in H by exact PRE. exact H.
Qed.
Lemma wrapper_frame_prefix_value : forall r before after d k q p j,
  wrapper_pre r -> k+q<=wrapper_n r -> j<=wrapper_n r ->
  (p=wrapper_sum r \/ p=wrapper_diff r) -> array_separate p d (wrapper_n r) ->
  wrapper_call_frame r before after (limb_ptr d k) (8*q) -> value after p j=value before p j.
Proof.
  intros r before after d k q p j PRE B J PTR SEP FRAME.
  replace p with (p+8*0) at 1 2 by lia.
  eapply wrapper_frame_operand_value; [exact PRE | lia | tauto | exact FRAME | ].
  unfold limb_ptr. apply noverlap_symmetry. rewrite noverlap_mod_idemp_l. apply noverlap_symmetry.
  replace (p+8*0) with (p+0) by lia.
  eapply noverlap_index_index; [exact SEP | nia | nia].
Qed.
Lemma wrapper_frame_metadata : forall r before after d k q offset,
  wrapper_pre r -> k+q<=wrapper_n r -> offset+8<=0x5a8 ->
  (d=wrapper_sum r \/ d=wrapper_diff r) ->
  wrapper_call_frame r before after (limb_ptr d k) (8*q) ->
  after Ⓠ[wrapper_frame r+offset]=before Ⓠ[wrapper_frame r+offset].
Proof.
  intros r before after d k q offset PRE K OFF D FRAME. apply FRAME.
  - eapply wrapper_stack_operand; eassumption.
  - eapply wrapper_stack_call_cell; eassumption.
Qed.
Lemma wrapper_frame_unread_disjoint : forall r before after d k q,
  wrapper_pre r -> k+q<=wrapper_n r ->
  array_separate (wrapper_u r) d (wrapper_n r) ->
  array_separate (wrapper_v r) d (wrapper_n r) ->
  wrapper_unread r before k ->
  wrapper_call_frame r before after (limb_ptr d k) (8*q) -> wrapper_unread r after k.
Proof.
  intros r before after d k q PRE K U V [UN VN] FRAME. unfold wrapper_unread,unread.
  split; etransitivity; [ | exact UN | | exact VN];
    eapply wrapper_frame_operand_value; [exact PRE | lia | tauto | exact FRAME | |
      exact PRE | lia | tauto | exact FRAME | ];
    unfold limb_ptr; apply noverlap_symmetry; rewrite noverlap_mod_idemp_l; apply noverlap_symmetry;
    eapply noverlap_index_index; [exact U | nia | nia | exact V | nia | nia].
Qed.
Lemma wrapper_alias_forward_safe : forall d p n,
  exact_or_separate d p n -> 8*n<=2^64 -> forward_safe d p n.
Proof. intros d p n [EQ|SEP] B; [subst p; apply forward_safe_same64,B | apply forward_safe_disjoint64,SEP]. Qed.
Lemma wrapper_frame_unread_advance : forall r before after d k q,
  wrapper_pre r -> k+q<=wrapper_n r -> (d=wrapper_sum r \/ d=wrapper_diff r) ->
  wrapper_unread r before k ->
  wrapper_call_frame r before after (limb_ptr d k) (8*q) -> wrapper_unread r after (k+q).
Proof.
  intros r before after d k q PRE K D UN FRAME.
  pose proof (unread_shrink _ _ _ _ _ _ _ UN K) as [U V].
  pose proof PRE as ROOT. destruct PRE as (MDL & BN & B & STACK & DISJ & ALIAS & SEP).
  assert (SU:forward_safe d (wrapper_u r) (wrapper_n r))
    by (apply wrapper_alias_forward_safe; [apply ALIAS; tauto | exact B]).
  assert (SV:forward_safe d (wrapper_v r) (wrapper_n r))
    by (apply wrapper_alias_forward_safe; [apply ALIAS; tauto | exact B]).
  unfold wrapper_unread,unread. split; etransitivity; [ | exact U | | exact V];
    eapply wrapper_frame_operand_value; [exact ROOT | lia | tauto | exact FRAME | |
      exact ROOT | lia | tauto | exact FRAME | ];
    unfold limb_ptr; apply noverlap_symmetry; rewrite noverlap_mod_idemp_l; apply noverlap_symmetry;
    eapply noverlap_index_r with (index:=8*k) (len2:=8*(k+q));
      [apply SU | nia | apply SV | nia]; lia.
Qed.

Lemma bounded_regions_separate64 : forall p a q b,
  p+a<=2^64 -> q+b<=2^64 -> (p+a<=q \/ q+b<=p) -> ~overlap 64 p a q b.
Proof. intros p a q b P Q ORDER [i [j [I [J EQ]]]]. rewrite !N.mod_small in EQ by lia. lia. Qed.
Lemma wrapper_scratch_stack_read : forall r offset size q,
  wrapper_pre r -> q<=170 -> offset+size<=0x5a8 ->
  (offset+size<=32 \/ 32+8*q<=offset) ->
  ~overlap 64 (wrapper_frame r+offset) size (wrapper_frame r+32) (8*q).
Proof.
  intros r offset size q PRE Q OFF ORDER.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  assert (B:r R_RSP<2^64) by exact (models_var R_RSP (proj1 PRE)).
  apply bounded_regions_separate64; unfold wrapper_frame; lia.
Qed.
Lemma wrapper_frame_scratch_metadata : forall r before after q offset,
  wrapper_pre r -> q<=170 -> offset+8<=32 ->
  wrapper_call_frame r before after (wrapper_frame r+32) (8*q) ->
  after Ⓠ[wrapper_frame r+offset]=before Ⓠ[wrapper_frame r+offset].
Proof.
  intros r before after q offset PRE Q OFF FRAME. apply FRAME.
  - eapply wrapper_scratch_stack_read; [exact PRE | exact Q | lia | left; exact OFF].
  - eapply wrapper_stack_call_cell; [exact PRE | lia].
Qed.
Lemma wrapper_frame_scratch_operand : forall r before after q p i j,
  wrapper_pre r -> q<=170 -> i+j<=wrapper_n r ->
  (p=wrapper_sum r \/ p=wrapper_diff r \/ p=wrapper_u r \/ p=wrapper_v r) ->
  wrapper_call_frame r before after (wrapper_frame r+32) (8*q) ->
  value after (p+8*i) j=value before (p+8*i) j.
Proof.
  intros r before after q p i j PRE Q IJ PTR FRAME.
  eapply wrapper_frame_operand_value; [exact PRE | exact IJ | exact PTR | exact FRAME | ].
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  pose proof (wrapper_operand_stack r p i j PRE PTR IJ) as SEP.
  unfold limb_ptr in SEP. rewrite noverlap_mod_idemp_l in SEP.
  replace (wrapper_frame r+32) with (wrapper_stack r+40) by (unfold wrapper_frame,wrapper_stack; lia).
  eapply noverlap_index_r; [exact SEP | nia].
Qed.
Lemma wrapper_frame_scratch_prefix : forall r before after q p j,
  wrapper_pre r -> q<=170 -> j<=wrapper_n r ->
  (p=wrapper_sum r \/ p=wrapper_diff r) ->
  wrapper_call_frame r before after (wrapper_frame r+32) (8*q) -> value after p j=value before p j.
Proof.
  intros. replace p with (p+8*0) at 1 2 by lia.
  eapply wrapper_frame_scratch_operand; eassumption || lia || tauto.
Qed.
Lemma wrapper_frame_scratch_unread : forall r before after q k,
  wrapper_pre r -> q<=170 -> k<=wrapper_n r -> wrapper_unread r before k ->
  wrapper_call_frame r before after (wrapper_frame r+32) (8*q) -> wrapper_unread r after k.
Proof.
  intros r before after q k PRE Q K [U V] FRAME. unfold wrapper_unread,unread.
  split; etransitivity; [ | exact U | | exact V];
    eapply wrapper_frame_scratch_operand; [exact PRE | exact Q | lia | tauto | exact FRAME |
      exact PRE | exact Q | lia | tauto | exact FRAME].
Qed.
Lemma wrapper_common_scratch_result : forall r caller after q,
  wrapper_pre r -> q<=170 -> wrapper_common r caller -> leaf_abi caller after ->
  wrapper_call_frame r (caller V_MEM64) (after V_MEM64) (wrapper_frame r+32) (8*q) ->
  wrapper_common r after.
Proof.
  intros r caller after q PRE Q (SP & LEN & SAVED & FRAME) ABI OUT.
  destruct ABI as (SP' & BX & BP & LEN' & REST). unfold wrapper_common.
  split; [congruence | ]. split; [congruence | ]. split.
  - eapply wrapper_frame_saved; [exact PRE | exact OUT | exact SAVED | ].
    intros offset OFF. eapply wrapper_scratch_stack_read; [exact PRE | exact Q | | ];
      destruct OFF as [-> | [-> | [-> | [-> | [-> | ->]]]]]; lia.
  - intros p len SUM DIFF STACK. transitivity (getmem 64 LittleE len (caller V_MEM64) p).
    + apply OUT.
      * assert (SB:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
        replace (wrapper_frame r+32) with (wrapper_stack r+40) by (unfold wrapper_frame,wrapper_stack; lia).
        eapply noverlap_index_r; [exact STACK | nia].
      * replace (wrapper_stack r) with (wrapper_stack r+0) at 1 by lia.
        eapply noverlap_index_r; [exact STACK | lia].
    + apply FRAME; assumption.
Qed.
