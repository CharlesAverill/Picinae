(* Arithmetic and memory facts used by all three wrapper chunk loops. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma chunk_size_bounds : forall n k,
  k<n -> 0<chunk_size n k /\ chunk_size n k<=170 /\ k+chunk_size n k<=n.
Proof. unfold chunk_size; intros; pose proof (N.le_min_l 170 (n-k));
  pose proof (N.le_min_r 170 (n-k)); split; [apply N.min_glb_lt; lia | split; lia]. Qed.
Lemma chunk_end_min : forall n k,
  k<=n -> chunk_end n k=N.min (k+170) n.
Proof.
  unfold chunk_end,chunk_size. intros n k B.
  destruct (N.le_ge_cases 170 (n-k)) as [LO|HI].
  - rewrite N.min_l, N.min_l by lia. reflexivity.
  - rewrite N.min_r, N.min_r by lia. lia.
Qed.

Lemma bounded_cells_separate : forall a b,
  a+8<=2^64 -> b+8<=2^64 -> (a+8<=b \/ b+8<=a) ->
  ~overlap 64 a 8 b 8.
Proof.
  intros a b A B ORDER [i [j [I [J EQ]]]].
  rewrite !N.mod_small in EQ by lia. lia.
Qed.

Definition wrapper_prologue_memory (r : store) :=
  (r V_MEM64)[Ⓠr R_RSP-8:=r R_R15][Ⓠr R_RSP-16:=r R_R14]
    [Ⓠr R_RSP-24:=r R_R13][Ⓠr R_RSP-32:=r R_R12]
    [Ⓠr R_RSP-40:=r R_RBP][Ⓠr R_RSP-48:=r R_RBX].

Lemma wrapper_prologue_saved : forall r,
  wrapper_pre r -> wrapper_saved r (wrapper_prologue_memory r).
Proof.
  intros r (MDL & BN & BYTES & STACK & REST).
  pose proof (models_var R_RSP MDL) as B. change (r R_RSP<2^64) in B.
  unfold wrapper_saved,wrapper_prologue_memory,wrapper_frame.
  replace (r R_RSP-0x5a8+0x578) with (r R_RSP-48) by lia.
  replace (r R_RSP-0x5a8+0x580) with (r R_RSP-40) by lia.
  replace (r R_RSP-0x5a8+0x588) with (r R_RSP-32) by lia.
  replace (r R_RSP-0x5a8+0x590) with (r R_RSP-24) by lia.
  replace (r R_RSP-0x5a8+0x598) with (r R_RSP-16) by lia.
  replace (r R_RSP-0x5a8+0x5a0) with (r R_RSP-8) by lia.
  repeat split;
    repeat first [rewrite getmem_setmem by (vm_compute; easy) |
      rewrite getmem_noverlap by (apply bounded_cells_separate; lia)];
    apply N.mod_small; match goal with |- r ?v < _ => exact (models_var v MDL) end.
Qed.

Lemma wrapper_prologue_frame : forall r,
  wrapper_pre r ->
  outside_output (r V_MEM64) (wrapper_prologue_memory r) (wrapper_stack r) 0x5b0.
Proof.
  intros r (MDL & BN & BYTES & STACK & REST).
  unfold wrapper_prologue_memory.
  replace (r R_RSP-8) with (wrapper_stack r+0x5a8) by (unfold wrapper_stack; lia).
  replace (r R_RSP-16) with (wrapper_stack r+0x5a0) by (unfold wrapper_stack; lia).
  replace (r R_RSP-24) with (wrapper_stack r+0x598) by (unfold wrapper_stack; lia).
  replace (r R_RSP-32) with (wrapper_stack r+0x590) by (unfold wrapper_stack; lia).
  replace (r R_RSP-40) with (wrapper_stack r+0x588) by (unfold wrapper_stack; lia).
  replace (r R_RSP-48) with (wrapper_stack r+0x580) by (unfold wrapper_stack; lia).
  repeat (apply outside_output_store; [vm_compute; easy | ]).
  apply outside_output_refl.
Qed.
Lemma wrapper_prologue_unread : forall r,
  wrapper_pre r -> wrapper_unread r (wrapper_prologue_memory r) 0.
Proof.
  intros r PRE. pose proof (wrapper_prologue_frame r PRE) as FRAME.
  destruct PRE as (MDL & BN & BYTES & STACK & DISJ & ALIAS & SEP).
  unfold wrapper_unread,unread. rewrite !N.mul_0_r,!N.add_0_r,!N.sub_0_r.
  split; apply FRAME.
  - exact (proj2 (SEP (wrapper_u r) ltac:(tauto))).
  - exact (proj2 (SEP (wrapper_v r) ltac:(tauto))).
Qed.
Lemma wrapper_prologue_memory_frame : forall r,
  wrapper_pre r -> wrapper_memory_frame r (wrapper_prologue_memory r).
Proof. intros r PRE p len SUM DIFF STACK; apply (wrapper_prologue_frame r PRE),STACK. Qed.
Lemma chunk_next_continue : forall n k,
  k<n -> k+170<n -> chunk_size n k=170 /\ chunk_end n k=k+170.
Proof. unfold chunk_end,chunk_size; intros; rewrite N.min_l by lia; split; reflexivity. Qed.
Lemma chunk_next_finish : forall n k,
  k<n -> n<=k+170 -> chunk_end n k=n.
Proof. intros; rewrite chunk_end_min, N.min_r by lia; reflexivity. Qed.
Lemma chunk_index_bounds : forall n k,
  n+170<2^63 -> k<n -> k+170<2^63 /\ 8*chunk_size n k<=2^64.
Proof. intros n k B K. pose proof (chunk_size_bounds n k K); split; lia. Qed.
Lemma chunk_index_multiple : forall k,
  k mod 170=0 -> (k+170) mod 170=0.
Proof. intros; rewrite N.Div0.add_mod, H; reflexivity. Qed.
Lemma limb_ptr_next : forall p k,
  (limb_ptr p k+0x550) mod 2^64=limb_ptr p (k+170).
Proof.
  intros. unfold limb_ptr. rewrite N.Div0.add_mod_idemp_l.
  f_equal. lia.
Qed.
Lemma limb_ptr_chunk : forall p k, limb_ptr p k=(p+8*k) mod 2^64.
Proof. reflexivity. Qed.

Lemma unread_chunk : forall m0 m u v n k q,
  k+q<=n -> unread m0 m u v n k ->
  value m (u+8*k) q=value m0 (u+8*k) q /\
  value m (v+8*k) q=value m0 (v+8*k) q.
Proof.
  intros m0 m u v n k q B [U V].
  unfold value,GMPArrayParams.w,GMPArrayParams.bytes in *.
  pose proof (getmem_inner 64 LittleE m m0 (8*(n-k)) (u+8*k) (u+8*k) 0 (8*q) U ltac:(nia)) as UQ.
  pose proof (getmem_inner 64 LittleE m m0 (8*(n-k)) (v+8*k) (v+8*k) 0 (8*q) V ltac:(nia)) as VQ.
  rewrite !N.add_0_r in UQ,VQ. split; assumption.
Qed.
Lemma wrapper_chunk_inputs : forall r m k,
  k<wrapper_n r -> wrapper_unread r m k ->
  value m (wrapper_u r+8*k) (chunk_size (wrapper_n r) k)=
    value (r V_MEM64) (wrapper_u r+8*k) (chunk_size (wrapper_n r) k) /\
  value m (wrapper_v r+8*k) (chunk_size (wrapper_n r) k)=
    value (r V_MEM64) (wrapper_v r+8*k) (chunk_size (wrapper_n r) k).
Proof. intros; eapply unread_chunk; [apply (proj2 (proj2 (chunk_size_bounds _ _ H))) | exact H0]. Qed.

(* A callee can alter the high chunk while preserving the committed prefix. *)
Lemma nc_chunk_append : forall sub m0 before after d u v k q cin c cout,
  nc_equation sub (value before d k) (value m0 u k) (value m0 v k) cin c k ->
  nc_equation sub (value after (d+8*k) q)
    (value m0 (u+8*k) q) (value m0 (v+8*k) q) c cout q ->
  value after d k=value before d k ->
  nc_equation sub (value after d (k+q))
    (value m0 u (k+q)) (value m0 v (k+q)) cin cout (k+q).
Proof.
  intros sub m0 before after d u v k q cin c cout PREFIX CHUNK FRAME.
  rewrite !value_add, FRAME. eapply nc_append; eassumption.
Qed.
Lemma outside_output_prefix : forall before after d k q,
  8*(k+q)<=2^64 -> outside_output before after (d+8*k) (8*q) ->
  value after d k=value before d k.
Proof.
  intros before after d k q B FRAME. apply FRAME.
  apply noverlap_adjacent64; nia.
Qed.
Lemma nc_chunk_append_frame : forall sub m0 before after d u v k q cin c cout,
  8*(k+q)<=2^64 -> outside_output before after (d+8*k) (8*q) ->
  nc_equation sub (value before d k) (value m0 u k) (value m0 v k) cin c k ->
  nc_equation sub (value after (d+8*k) q)
    (value m0 (u+8*k) q) (value m0 (v+8*k) q) c cout q ->
  nc_equation sub (value after d (k+q))
    (value m0 u (k+q)) (value m0 v (k+q)) cin cout (k+q).
Proof. intros; eapply nc_chunk_append; try eassumption; eapply outside_output_prefix; eassumption. Qed.

Lemma unread_after_output : forall m0 before after d u v n k q,
  k+q<=n -> forward_safe d u n -> forward_safe d v n ->
  unread m0 before u v n k -> outside_output before after (d+8*k) (8*q) ->
  unread m0 after u v n (k+q).
Proof.
  intros m0 before after d u v n k q B SU SV UN FRAME.
  pose proof (unread_shrink _ _ _ _ _ _ _ UN B) as [U V].
  unfold unread. split; etransitivity; [apply FRAME | exact U | apply FRAME | exact V];
    eapply noverlap_index_r with (index:=8*k) (len2:=8*(k+q));
    [apply SU | |apply SV | ]; lia.
Qed.

Lemma wrapper_results_zero : forall r m, wrapper_results r m 0 0 0 0.
Proof. intros. unfold wrapper_results,nc_equation. rewrite !value_zero. repeat split; lia. Qed.
Lemma wrapper_results_post : forall r s cy borrow,
  wrapper_results r (s V_MEM64) (wrapper_n r) (wrapper_n r) cy borrow ->
  s R_RAX=2*cy+borrow ->
  add_n_sub_n_post (r V_MEM64) (wrapper_sum r) (wrapper_diff r)
    (wrapper_u r) (wrapper_v r) (wrapper_n r) s.
Proof. unfold wrapper_results,add_n_sub_n_post; intros; exists cy,borrow; tauto. Qed.
Lemma wrapper_scratch_commit : forall r before after k q cy,
  wrapper_scratch_sum r before k q cy ->
  value after (wrapper_sum r) k=value before (wrapper_sum r) k ->
  value after (wrapper_sum r+8*k) q=value before (wrapper_frame r+0x20) q ->
  cy<=1 /\ nc_equation false (value after (wrapper_sum r) (k+q))
    (value (r V_MEM64) (wrapper_u r) (k+q))
    (value (r V_MEM64) (wrapper_v r) (k+q)) 0 cy (k+q).
Proof. intros r before after k q cy [B EQ] LOW HIGH. rewrite value_add, LOW, HIGH; tauto. Qed.

Lemma wrapper_memory_frame_refl : forall r, wrapper_memory_frame r (r V_MEM64).
Proof. unfold wrapper_memory_frame; intros; reflexivity. Qed.
Lemma wrapper_memory_frame_output : forall r before after d k q,
  d=wrapper_sum r \/ d=wrapper_diff r -> k+q<=wrapper_n r ->
  wrapper_memory_frame r before -> outside_output before after (d+8*k) (8*q) ->
  wrapper_memory_frame r after.
Proof.
  intros r before after d k q D B FRAME OUT p len SUM DIFF STACK.
  transitivity (getmem 64 LittleE len before p); [apply OUT | apply FRAME; assumption].
  destruct D as [-> | ->]; eapply noverlap_index_r; [exact SUM | |exact DIFF | ]; nia.
Qed.
Lemma wrapper_memory_frame_stack : forall r m offset size out,
  offset+size<=0x5b0 -> wrapper_memory_frame r m ->
  wrapper_memory_frame r (setmem 64 LittleE size m (wrapper_stack r+offset) out).
Proof.
  unfold wrapper_memory_frame. intros r m offset size out B FRAME p len SUM DIFF STACK.
  rewrite getmem_noverlap; [apply FRAME; assumption | ].
  eapply noverlap_index_r; eassumption.
Qed.
Lemma wrapper_stack_preserves_array : forall r m p n offset size out,
  ~overlap 64 p (8*n) (wrapper_stack r) 0x5b0 -> offset+size<=0x5b0 ->
  value (setmem 64 LittleE size m (wrapper_stack r+offset) out) p n=value m p n.
Proof. intros; apply getmem_noverlap; eapply noverlap_index_r; eassumption. Qed.

Lemma wrapper_saved_frame : forall r before after d q,
  (forall offset, offset=0x578 \/ offset=0x580 \/ offset=0x588 \/
                  offset=0x590 \/ offset=0x598 \/ offset=0x5a0 ->
    ~overlap 64 (wrapper_frame r+offset) 8 d (8*q)) ->
  wrapper_saved r before -> outside_output before after d (8*q) ->
  wrapper_saved r after.
Proof.
  intros r before after d q SEP SAVED OUT. unfold wrapper_saved in *.
  rewrite (OUT (wrapper_frame r+0x578) 8), (OUT (wrapper_frame r+0x580) 8),
    (OUT (wrapper_frame r+0x588) 8), (OUT (wrapper_frame r+0x590) 8),
    (OUT (wrapper_frame r+0x598) 8), (OUT (wrapper_frame r+0x5a0) 8);
    try (apply SEP; tauto).
  exact SAVED.
Qed.

Lemma wrapper_metadata_outside : forall r m offset out,
  wrapper_pre r -> offset+8<=0x578 ->
  outside_output m (m[Ⓠwrapper_frame r+offset:=out]) (wrapper_stack r) 0x5b0.
Proof.
  intros r m offset out PRE B.
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  replace (wrapper_frame r+offset) with (wrapper_stack r+(8+offset))
    by (unfold wrapper_frame,wrapper_stack; lia).
  apply outside_output_store; [lia | apply outside_output_refl].
Qed.
Lemma wrapper_common_metadata : forall r s offset out,
  wrapper_pre r -> offset+8<=0x578 -> wrapper_common r s ->
  wrapper_common r (s[V_MEM64:=(s V_MEM64)[Ⓠwrapper_frame r+offset:=out]]).
Proof.
  intros r s offset out PRE OFF (SP & LEN & SAVED & FRAME).
  assert (STACK:0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  pose proof (models_var R_RSP (proj1 PRE)) as B. change (r R_RSP<2^64) in B.
  unfold wrapper_common. repeat (rewrite update_updated || rewrite update_frame by discriminate).
  split; [exact SP | ]. split; [exact LEN | ]. split.
  - unfold wrapper_saved in SAVED |- *.
    repeat rewrite getmem_noverlap by
      (apply bounded_cells_separate; unfold wrapper_frame; lia). exact SAVED.
  - intros p len SUM DIFF STK. rewrite getmem_noverlap.
    + apply FRAME; assumption.
    + replace (wrapper_frame r+offset) with (wrapper_stack r+(8+offset))
        by (unfold wrapper_frame,wrapper_stack; lia).
      eapply noverlap_index_r; [exact STK | lia].
Qed.
Lemma wrapper_metadata_array : forall r m offset out p j,
  wrapper_pre r -> offset+8<=0x578 -> j<=wrapper_n r ->
  (p=wrapper_sum r \/ p=wrapper_diff r \/ p=wrapper_u r \/ p=wrapper_v r) ->
  value (m[Ⓠwrapper_frame r+offset:=out]) p j=value m p j.
Proof.
  intros r m offset out p j PRE OFF J PTR.
  pose proof (wrapper_metadata_outside r m offset out PRE OFF) as OUT.
  destruct PRE as (MDL & BN & BYTES & STACK & DISJ & ALIAS & SEP).
  apply OUT. change (~overlap 64 p (8*j) (wrapper_stack r) 0x5b0).
  replace p with (p+0) at 1 by lia.
  eapply noverlap_index_l; [exact (proj2 (SEP p PTR)) | lia].
Qed.
Lemma wrapper_results_metadata : forall r m offset out ks kd cy borrow,
  wrapper_pre r -> offset+8<=0x578 -> ks<=wrapper_n r -> kd<=wrapper_n r ->
  wrapper_results r m ks kd cy borrow ->
  wrapper_results r (m[Ⓠwrapper_frame r+offset:=out]) ks kd cy borrow.
Proof.
  intros r m offset out ks kd cy borrow PRE OFF KS KD POST.
  unfold wrapper_results. rewrite !wrapper_metadata_array by (try assumption; tauto). exact POST.
Qed.
Lemma wrapper_unread_metadata : forall r m offset out k,
  wrapper_pre r -> offset+8<=0x578 -> k<=wrapper_n r ->
  wrapper_unread r m k -> wrapper_unread r (m[Ⓠwrapper_frame r+offset:=out]) k.
Proof.
  intros r m offset out k PRE OFF K [U V].
  pose proof (wrapper_metadata_outside r m offset out PRE OFF) as OUT.
  destruct PRE as (MDL & BN & BYTES & STACK & DISJ & ALIAS & SEP).
  unfold wrapper_unread,unread. split; etransitivity; [apply OUT | exact U | apply OUT | exact V];
    eapply noverlap_index_l; [exact (proj2 (SEP (wrapper_u r) ltac:(tauto))) | |
                             exact (proj2 (SEP (wrapper_v r) ltac:(tauto))) | ]; unfold GMPArrayParams.bytes; lia.
Qed.
