(* Complete-strategy composition attempt, GPT-6.1 Sol, November 2026.
   Same inherited Ubuntu 2.35-0ubuntu3.12 SHA256
   9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
   unchanged memcpy_amd64 lift and hardware/lifting boundaries documented
   in amd64_memcpy_nt_head_proof. System V AMD64 RDI=d, RSI=s, RDX=n,
   RSP=rsp; at the actual RET cuts RAX=d, RSP=rsp, original-source copy
   with the complete outside-destination byte frame. Callee-saved registers
   use memcpy_preserves_callee_saved. IL partial correctness only; no
   termination, CPU-feature, ordering/cache, fault or lifter-soundness claim.
   Domain: n>128, modular nov, d+n<2^64, initial threshold<n, and the exact
   selected-path positive-counter domain nt_strategy_domain, which uses the
   threshold AFTER the four head stores. No artificial upper-size cap. *)
Require Import Picinae_amd64 memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memcpy_proof
  amd64_memcpy_loops_proof amd64_memcpy_nt_proof
  amd64_memcpy_nt_dispatch_proof amd64_memcpy_nt_head_proof
  amd64_memcpy_nt_domain_proof amd64_memcpy_nt_bulk_proof amd64_memcpy_nt_bulk4_proof.
Import ListNotations.
Open Scope N.

Definition nt_strategy_invs m d s n rsp (t:trace) :=
 match t with (Addr a,st)::_ => match a with
 | 1853552 => Some (nt_dispatch_state m d s n rsp st)
 | 1854064 => Some (nt_dispatch_state m d s n rsp st /\ st R_RAX=d /\ xmm_ok st R_YMM0 m s)
 | 1854381 => Some (nt_head_input m d s n rsp st)
 | 1854420 => Some (nt_head_stored m d s n rsp st)
 | 1854454 => Some (nt_head_aligned m d s n rsp st /\ ~nt_alias d s)
 | 1854474 => Some (nt_head_aligned m d s n rsp st /\
                    ~nt_four_selected m d s n /\ st R_R10=(n-nt_align d)>>4)
 | 1854768 => Some (nt_head_aligned m d s n rsp st /\ nt_four_selected m d s n)
 | 1854501 => Some (exists j i, nt_bulk_state false m d s n rsp j i st)
 | 1854789 => Some (exists j i, nt_bulk_state true m d s n rsp j i st)
 | 1854659 => Some (nt_bulk_post false m d s n rsp st)
 | 1855083 => Some (nt_bulk_post true m d s n rsp st)
 | 1854667 | 1855091 => Some (exists c, c+64<n /\ nt_tail_state m d s n rsp c st)
 | 1854721 | 1855145 => Some (exists c, n-64<=c /\ nt_tail_state m d s n rsp c st)
 | 1854761 | 1855185 => Some (postcondition m d s n rsp st)
 | 1854092 | 1854224 | 1854114 => Some False
 | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 | 1854063 => Some False
 | _ => None end | _ => None end.

Lemma nt_strategy_entry_step: forall m d s n rsp st t,
  models archtyps st -> 128<n -> nt_dispatch_state m d s n rsp st ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1853552,st)::t).
Proof.
  intros m d s n rsp st t MDL BIG [MEM [D [S [NN RSP]]]].
  repeat step_prune.
  split; [change (m=m /\ d=d /\ s=s /\ n=n /\ st R_RSP=rsp);
    repeat split; try reflexivity; exact RSP|].
  split; [reflexivity|]. unfold xmm_ok. psimpl. pack_xmm. reflexivity.
Qed.

Lemma nt_strategy_dispatch_step: forall m d s n rsp st t,
  models archtyps st -> 128<n -> nov d s n -> m Ⓠ[0x3215a8]<n ->
  nt_dispatch_state m d s n rsp st /\ st R_RAX=d /\ xmm_ok st R_YMM0 m s ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854064,st)::t).
Proof.
  intros m d s n rsp st t MDL BIG NOV THR
    [[MEM [D [S [NN RSP]]]] [RAX X0]].
  assert (DSN: n<=d ⊖ s) by (apply nov_ds; [exact NOV|clear - BIG; lia]).
  repeat x64_step.
  all: set (T:=m Ⓠ[0x3215a8]) in *; clearbody T.
  all: try (exfalso; apply N.ltb_lt in BC; clear - BC DSN; lia).
  all: try (exfalso; apply ja_not_taken in BC0; destruct BC0 as [B|B];
    [apply N.ltb_lt in B|apply N.eqb_eq in B]; clear - B THR; lia).
  split; [change (m=m /\ d=d /\ s=s /\ n=n /\ st R_RSP=rsp);
    repeat split; try reflexivity; exact RSP|].
  split; [change (st R_RAX=d); exact RAX|].
  split; [change (xmm_ok st R_YMM0 m s); exact X0|]. reflexivity.
Qed.

Lemma nt_strategy_setup2: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> n<2^64 -> 64<=n ->
  nt_strategy_domain m d s n ->
  nt_head_aligned m d s n rsp st /\ ~nt_four_selected m d s n /\
    st R_R10=(n-nt_align d)>>4 ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854474,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV NB BIG DOMAIN
    [[MEM [D [S [NN [AX SP]]]]] [SEL R10]].
  pose proof (nt_selected_counter_positive m d s n false DOMAIN SEL) as POS.
  change (0<nt_count false d n) in POS.
  pose proof (nt_head_copy m d s n BIG NOV NB) as COPY.
  repeat x64_step.
  exists 0, 0. unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
  nt_scalar_projections.
  split; [exact POS|]. split; [reflexivity|]. split.
  - rewrite ?MEM. eapply cpy_equiv; [|exact COPY]. intro x. symmetry. apply nt_done_initial.
  - rewrite !N.mul_0_r, !N.add_0_r, !N.sub_0_r.
    split; [exact D|]. split; [exact S|]. split; [reflexivity|].
    split.
    + unfold nt_count, nt_chunk, nt_pages.
      rewrite N.shiftr_div_pow2. reflexivity.
    + split; [unfold nt_rest, nt_chunk, nt_pages; reflexivity|].
      split; first [exact AX|exact SP|reflexivity].
Qed.

Lemma nt_strategy_setup4: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> n<2^64 -> 64<=n ->
  nt_strategy_domain m d s n ->
  nt_head_aligned m d s n rsp st /\ nt_four_selected m d s n ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854768,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV NB BIG DOMAIN
    [[MEM [D [S [NN [AX SP]]]]] SEL].
  pose proof (nt_selected_counter_positive m d s n true DOMAIN SEL) as POS.
  change (0<nt_count true d n) in POS.
  pose proof (nt_head_copy m d s n BIG NOV NB) as COPY.
  repeat x64_step.
  exists 0, 0. unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
  nt_scalar_projections.
  split; [exact POS|]. split; [reflexivity|]. split.
  - rewrite ?MEM. eapply cpy_equiv; [|exact COPY]. intro x. symmetry. apply nt_done_initial.
  - rewrite !N.mul_0_r, !N.add_0_r, !N.sub_0_r.
    split; [exact D|]. split; [exact S|]. split; [reflexivity|].
    split.
    + unfold nt_count, nt_chunk, nt_pages.
      rewrite N.shiftr_div_pow2. reflexivity.
    + split; [unfold nt_rest, nt_chunk, nt_pages; reflexivity|].
      split; first [exact AX|exact SP|reflexivity].
Qed.

Lemma nt_strategy_jbe_not: forall a b:bool,
  ((if a then 1 else 0) .| (if b then 1 else 0))=0 -> a=false /\ b=false.
Proof. intros [|] [|]; cbn; intro H; first [discriminate|tauto]. Qed.
Lemma nt_strategy_jbe_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0))=N.pos p -> a=true \/ b=true.
Proof. intros [|] [|] p; cbn; intro H; first [discriminate|tauto]. Qed.

Lemma nt_strategy_tail_join: forall (four:bool) m d s n rsp c st t,
  models archtyps st -> nt_tail_state m d s n rsp c st ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr (if four then 1855083 else 1854659),st)::t).
Proof.
  intros four m d s n rsp c st t MDL
    [CU [REM [C [D [S [DX [AX SP]]]]]]].
  destruct four; repeat x64_step.
  all: exists c; split.
  all: try (lazymatch goal with |- _+64 < _ => idtac end;
    apply nt_strategy_jbe_not in BC; destruct BC as [B1 B2];
    apply N.ltb_ge in B1; apply N.eqb_neq in B2;
    rewrite N.mod_small in B1, B2 by exact REM; clear - B1 B2; lia).
  all: try (lazymatch goal with |- _ <= _ => idtac end;
    apply nt_strategy_jbe_taken in BC; destruct BC as [B|B];
    [apply N.ltb_lt in B|apply N.eqb_eq in B];
    rewrite N.mod_small in B by exact REM; clear - B; lia).
  all: unfold nt_tail_state; nt_scalar_projections;
    split; [exact CU|]; split; [exact REM|]; split; [exact C|];
    split; [first [reflexivity|exact D]|];
    split; [first [reflexivity|exact S]|];
    split; [first [reflexivity|exact DX]|]; split; assumption.
Qed.

Lemma nt_head_store_segment_strategy: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> 64<=n ->
  nt_head_input m d s n rsp st ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854381,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV BIG PRE.
  destruct PRE as [[MEM [D [S [NN RSP]]]] [RAX [X0 RCX]]].
  assert (SD: n<=s ⊖ d) by (apply nov_sd; [exact NOV|clear - BIG; lia]).
  assert (SB: s<2^64) by (rewrite <-S; exact (MDL R_RSI 64 eq_refl)).
  repeat x64_step.
  all: rewrite ?nt_neg_distance, ?nt_neg_add in *.
  all: try (match goal with |- False => idtac end;
    exfalso; apply ja_taken in BC; destruct BC as [B1 B2];
    apply N.ltb_ge in B1; apply N.eqb_neq in B2;
    assert (E: n=s ⊖ d) by (clear - B1 SD; lia);
    apply B2; rewrite E, N.add_comm, addmsub, N.mod_small by exact SB; reflexivity).
  unfold nt_head_stored, nt_head_memory, nt_row.
    rewrite ?pack16. pack_xmm.
    split.
    + rewrite <- (setmem_mod_r 64 LittleE 16 _ _ (st R_YMM0)).
      change (2^(16*8)) with (2^128). unfold xmm_ok in X0. rewrite X0.
      rewrite !N.add_0_r.
      replace (16+d) with (d+16) by (clear; lia).
      replace (32+d) with (d+32) by (clear; lia).
      replace (48+d) with (d+48) by (clear; lia).
      replace (16+s) with (s+16) by (clear; lia).
      replace (32+s) with (s+32) by (clear; lia).
      replace (48+s) with (s+48) by (clear; lia).
      reflexivity.
    + change (d=d /\ s=s /\ n=n /\ st R_RAX=d /\ st R_RSP=rsp /\ s ⊖ d=s ⊖ d).
      repeat split; first [reflexivity|assumption].
Qed.

Lemma nt_head_align_segment_strategy: forall m d s n rsp st t,
  models archtyps st -> d+n<2^64 -> 64<=n -> n<2^64 ->
  nt_head_stored m d s n rsp st ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854420,st)::t).
Proof.
  intros m d s n rsp st t MDL NW BIG NB PRE.
  destruct PRE as [MEM [D [S [NN [RAX [RSP RCX]]]]]].
  pose proof (nt_align_bounds d) as A.
  pose proof (N.mod_lt d 64 ltac:(discriminate)) as DM.
  repeat x64_step.
  all: split.
  all: try (unfold nt_head_aligned; split;
    [change (st V_MEM64=nt_head_memory m d s); exact MEM|]; split;
    [change (msub 64 (64+d) (d mod 64)=d+nt_align d);
     rewrite msub_sub by (clear - DM; lia);
     rewrite N.mod_small by (clear - NW BIG DM; lia);
     unfold nt_align; clear - DM; lia|]; split;
    [change (msub 64 (64+s) (d mod 64)=s ⊕ nt_align d);
     rewrite msub_sub by (clear - DM; lia);
     unfold nt_align; f_equal; clear - DM; lia|]; split;
    [change (msub 64 (n+d mod 64) 64=n-nt_align d);
     rewrite msub_sub by (clear - BIG; lia);
     rewrite N.mod_small by (clear - DM NB; lia);
     unfold nt_align; clear - DM BIG; lia|];
    change (st R_RAX=d /\ st R_RSP=rsp); split; assumption).
  all: unfold nt_four_selected, nt_alias.
  all: first [left; apply N.eqb_eq; exact BC | apply N.eqb_neq; exact BC].
Qed.

Lemma nt_head_threshold_segment_strategy: forall m d s n rsp st t,
  models archtyps st ->
  nt_head_aligned m d s n rsp st /\ ~nt_alias d s ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854454,st)::t).
Proof.
  intros m d s n rsp st t MDL [[MEM [D [S [NN [RAX RSP]]]]] ALIAS].
  repeat x64_step.
  all: unfold nt_four_selected.
  all: set (T:=nt_head_memory m d s Ⓠ[0x3215a8]) in *; clearbody T.
  all: split; [unfold nt_head_aligned; repeat split; first [reflexivity|assumption]|].
  - split.
    + intros [H|H]; [exact (ALIAS H)|].
      apply N.ltb_lt in BC. clear - BC H. lia.
    + reflexivity.
  - right. apply N.ltb_ge in BC. exact BC.
Qed.

Lemma nt_bulk_iteration2_strategy: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> d+n<2^64 -> n<2^64 -> 64<=n ->
  (exists j i, nt_bulk_state false m d s n rsp j i st) ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854501,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV NW NB BIG PRE.
  destruct PRE as [j [i [J [I [C [D [S [CX [R10 [DX [AX SP]]]]]]]]]]].
  pose proof (nt_align_bounds d) as A.
  destruct (nt_count_bounds false d n BIG) as [CK [REST RB]].
  assert (B: nt_align d+4096*2*(j+1)<=n)
    by (change (nt_chunk false) with 8192 in CK; clear - CK J; nia).
  pose proof (nt_image2_advance m (st V_MEM64) d s n (nt_align d) j i A I B NOV NB C) as ADV.
  change (4096*2) with (2^13) in ADV.
  rewrite (nt_image2_at (st V_MEM64) d s (nt_align d) (2^13) j i) in ADV.
  unfold nt_offset, nt_chunk, nt_pages in D, S, CK, REST, RB.
  repeat x64_step.
  all: rewrite ?pack16; pack_xmm.
  all: change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  all: lazymatch type of ADV with cpy _ ?MP _ _ _ =>
    set (Mpost:=MP) in *; clearbody Mpost end.
  all: change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  all: change (nt_chunk false) with 8192 in *.
  - apply N.eqb_eq in BC. apply N.eqb_eq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count false d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    assert (JE: j+1=nt_count false d n) by (clear - BC0 J; lia).
    unfold nt_bulk_post, nt_tail_state.
    split; [clear - CK; lia|]. split; [clear - RB REST; lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. rewrite nt_done_chunk by reflexivity.
      rewrite JE. clear - A JE. intuition nia.
    + split.
      *         rewrite N.mod_small by (clear - NW B I; nia).
        clear - IE JE; nia.
      * split.
        --            f_equal. clear - IE JE; nia.
        -- split; [rewrite DX; clear - REST; lia|]. split; assumption.
  - apply N.eqb_eq in BC. apply N.eqb_neq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count false d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    exists (j+1), 0. unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [clear - J BC0; lia|]. split; [lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. apply nt_done_next_chunk. reflexivity.
    + split.
      * rewrite N.mod_small by (clear - NW B I; nia). clear - IE; nia.
      * split; [f_equal; clear - IE; nia|]. split; [lia|].
        split; [rewrite msub_sub by (clear - J; lia);
          rewrite N.mod_small by (clear - CB J; lia); clear - J; lia|].
        split; [exact DX|]. split; assumption.
  - apply N.eqb_neq in BC.
    exists j, (i+1). unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [exact J|]. split; [clear - BC I; lia|]. split; [exact ADV|].
    split; [rewrite N.mod_small by (clear - NW B I; nia); clear; nia|].
    split; [f_equal; clear; nia|].
    split; [rewrite msub_sub by (clear - I; lia);
      rewrite N.mod_small by (clear - I; lia); clear - I; lia|].
    split; [exact R10|]. split; [exact DX|]. split; assumption.
Qed.

Lemma nt_bulk_iteration4_strategy: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> d+n<2^64 -> n<2^64 -> 64<=n ->
  (exists j i, nt_bulk_state true m d s n rsp j i st) ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr 1854789,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV NW NB BIG PRE.
  destruct PRE as [j [i [J [I [C [D [S [CX [R10 [DX [AX SP]]]]]]]]]]].
  pose proof (nt_align_bounds d) as A.
  destruct (nt_count_bounds true d n BIG) as [CK [REST RB]].
  assert (B: nt_align d+4096*4*(j+1)<=n)
    by (change (nt_chunk true) with 16384 in CK; clear - CK J; nia).
  pose proof (nt_image4_advance m (st V_MEM64) d s n (nt_align d) j i A I B NOV NB C) as ADV.
  change (4096*4) with (2^14) in ADV.
  rewrite (nt_image4_at (st V_MEM64) d s (nt_align d) (2^14) j i) in ADV.
  unfold nt_offset, nt_chunk, nt_pages in D, S, CK, REST, RB.
  do 29 x64_step.
  rewrite ?pack16. pack_xmm.
  x64_step.
  change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  pose proof (nt_image2_at (st V_MEM64) d s (nt_align d) (2^14) j i) as HALF.
  lazymatch type of HALF with _ = ?MP =>
    set (Mhalf:=MP) in *; clear HALF; clearbody Mhalf end.
  do 7 x64_step.
  rewrite ?pack16. pack_xmm.
  x64_step.
  change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  lazymatch type of ADV with cpy _ ?MP _ _ _ =>
    set (Mpost:=MP) in *; clearbody Mpost end.
  repeat x64_step.
  all: change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  all: change (nt_chunk true) with 16384 in *.
  - apply N.eqb_eq in BC. apply N.eqb_eq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count true d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    assert (JE: j+1=nt_count true d n) by (clear - BC0 J; lia).
    unfold nt_bulk_post, nt_tail_state.
    split; [clear - CK; lia|]. split; [clear - RB REST; lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. rewrite nt_done_chunk by reflexivity.
      rewrite JE. clear - A JE. intuition nia.
    + split.
      *         rewrite N.mod_small by (clear - NW B I; nia).
        clear - IE JE; nia.
      * split.
        --            f_equal. clear - IE JE; nia.
        -- split; [rewrite DX; clear - REST; lia|]. split; assumption.
  - apply N.eqb_eq in BC. apply N.eqb_neq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count true d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    exists (j+1), 0. unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [clear - J BC0; lia|]. split; [lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. apply nt_done_next_chunk. reflexivity.
    + split.
      * rewrite N.mod_small by (clear - NW B I; nia). clear - IE; nia.
      * split; [f_equal; clear - IE; nia|]. split; [lia|].
        split; [rewrite msub_sub by (clear - J; lia);
          rewrite N.mod_small by (clear - CB J; lia); clear - J; lia|].
        split; [exact DX|]. split; assumption.
  - apply N.eqb_neq in BC.
    exists j, (i+1). unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [exact J|]. split; [clear - BC I; lia|]. split; [exact ADV|].
    split; [rewrite N.mod_small by (clear - NW B I; nia); clear; nia|].
    split; [f_equal; clear; nia|].
    split; [rewrite msub_sub by (clear - I; lia);
      rewrite N.mod_small by (clear - I; lia); clear - I; lia|].
    split; [exact R10|]. split; [exact DX|]. split; assumption.
Qed.

Lemma nt_tail_final_strategy: forall (four:bool) m d s n rsp st t,
  nov d s n -> n < 2^64 -> 64 <= n -> models archtyps st ->
  (exists c, n - 64 <= c /\ nt_tail_state m d s n rsp c st) ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr (if four then 1855145 else 1854721), st)::t).
Proof.
  intros four m d s n rsp st t NOV NB BIG MDL PRE.
  destruct PRE as [c [CL [CU [REM [C [RDI [RSI [RDX [RAX RSP]]]]]]]]].
  destruct four; repeat x64_step.
  all: rewrite ?pack16.
  all: split; [exact RAX|]; split; [exact RSP|].
  all: eapply cpy_copied; cycle 1.
  all: try (eapply (cpy_store4 m (st V_MEM64) d s n (fun x => x < c)
                    (n-64) (n-48) (n-32) (n-16));
    [exact C | intros i I; clear - CU I; lia | exact NOV | exact NB | ..];
    try (clear - BIG; lia);
    rewrite nt_tail_addr by (clear - BIG CU; change (2^64) with 18446744073709551616; lia);
    reflexivity).
  all: intro i; clear - CL CU BIG; split; intro H; repeat destruct H as [H|H]; lia.
Qed.

Lemma nt_tail_loop_strategy: forall (four:bool) m d s n rsp st t,
  nov d s n -> n < 2^64 -> d + n < 2^64 -> models archtyps st ->
  (exists c, c + 64 < n /\ nt_tail_state m d s n rsp c st) ->
  nextinv memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit false
    ((Addr (if four then 1855091 else 1854667), st)::t).
Proof.
  intros four m d s n rsp st t NOV NB NW MDL PRE.
  destruct PRE as [c [CL [CU [REM [C [RDI [RSI [RDX [RAX RSP]]]]]]]]].
  assert (RE: msub 32 (n-c) 64 = n-(c+64)).
  { rewrite nt_remainder_sub by (clear - CL REM; lia). clear - CL; lia. }
  destruct four; repeat x64_step.
  all: rewrite ?pack16.
  all: assert (ADV: cpy m
      ((st V_MEM64) [Ⓧ d+c := st V_MEM64 Ⓧ[s+c]]
        [Ⓧ 16+d+c := st V_MEM64 Ⓧ[16+s+c]]
        [Ⓧ 32+d+c := st V_MEM64 Ⓧ[32+s+c]]
        [Ⓧ 48+d+c := st V_MEM64 Ⓧ[48+s+c]]) d s (fun x => x < c+64)).
  all: try (eapply cpy_equiv; [|eapply (cpy_store4 m (st V_MEM64) d s n (fun x => x<c)
                      c (c+16) (c+32) (c+48));
     [exact C|intros x X; clear - X CU; lia|exact NOV|exact NB|..]];
     [intro x; clear; lia|..]; clear - CL; first [lia|f_equal; lia]).
  all: exists (c+64); split.
  all: try (apply ja_not_taken in BC; destruct BC as [BC|BC];
      [apply N.ltb_lt in BC; rewrite RE in BC|
       apply N.eqb_eq in BC; rewrite N.mod_small in BC by exact REM];
      clear - BC CL; lia).
  all: try (apply ja_taken in BC; destruct BC as [B1 B2];
      apply N.ltb_ge in B1; apply N.eqb_neq in B2;
      rewrite RE in B1; rewrite N.mod_small in B2 by exact REM;
      clear - B1 B2 CL; lia).
  all: unfold nt_tail_state; split; [clear - CL; lia|];
    split; [clear - REM; lia|]; split; [exact ADV|].
  all: split; [change (64 + d ⊕ c = d + (c+64));
    rewrite N.mod_small by (clear - NW CL; lia); clear; lia|].
  all: split; [change (64 + s ⊕ c = s ⊕ (c+64)); f_equal; clear; lia|].
  all: split; [exact RE|]; split; [exact RAX|exact RSP].
Qed.

Theorem memcpy_correct_nt_strategy:
  forall st t st' x' m d s n rsp
    (ENTRY: startof t (x',st')=(Addr 1853552,st))
    (MDL: models x64typctx st) (PRE: nt_dispatch_state m d s n rsp st)
    (BIG: 128<n) (NOV: nov d s n) (NW: d+n<2^64)
    (THR: m Ⓠ[0x3215a8]<n) (DOMAIN: nt_strategy_domain m d s n),
  satisfies_all memcpy_amd64 (nt_strategy_invs m d s n rsp) nt_tail_exit ((x',st')::t).
Proof.
  intros.
  assert (NB: n<2^64) by (destruct PRE as [_ [_ [_ [NN _]]]];
    rewrite <-NN; exact (MDL R_RDX 64 eq_refl)).
  assert (BIG64: 64<=n) by (clear - BIG; lia).
  apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. exact PRE.
  - intros. erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
    clear - PRE0 MDL1 BIG BIG64 NOV NW NB THR DOMAIN. rename t1 into t.
    destruct_inv 64 PRE0.
    all: first
      [apply nt_strategy_entry_step; assumption
      |apply nt_strategy_dispatch_step; assumption
      |apply nt_head_store_segment_strategy; assumption
      |apply nt_head_align_segment_strategy; assumption
      |apply nt_head_threshold_segment_strategy; assumption
      |apply nt_strategy_setup2; assumption
      |apply nt_strategy_setup4; assumption
      |apply nt_bulk_iteration2_strategy; assumption
      |apply nt_bulk_iteration4_strategy; assumption
      |apply (nt_strategy_tail_join false m d s n rsp
        (nt_align d+nt_chunk false*nt_count false d n)); assumption
      |apply (nt_strategy_tail_join true m d s n rsp
        (nt_align d+nt_chunk true*nt_count true d n)); assumption
      |apply (nt_tail_loop_strategy false); assumption
      |apply (nt_tail_loop_strategy true); assumption
      |apply (nt_tail_final_strategy false); assumption
      |apply (nt_tail_final_strategy true); assumption].
Qed.

Theorem memcpy_nt_strategy_nonvacuous: forall (four:bool),
  exists st m d s n rsp,
    models x64typctx st /\ nt_dispatch_state m d s n rsp st /\
    128<n /\ nov d s n /\ d+n<2^64 /\ m Ⓠ[0x3215a8]<n /\
    nt_strategy_domain m d s n /\
    (if four then nt_four_selected m d s n else ~nt_four_selected m d s n).
Proof.
  intro four. set (threshold:=if four then 0 else 4096).
  exists (nt_head_witness threshold), (0 [Ⓠ0x3215a8:=threshold]),
    65536, 131072, 16448, 0.
  destruct (memcpy_nt_head_nonvacuous threshold) as [MDL [INPUT [NOV [NW [BIG NB]]]]].
  split; [exact MDL|]. split; [exact (proj1 INPUT)|].
  split; [reflexivity|]. split; [exact NOV|]. split; [exact NW|].
  split; [rewrite getmem_setmem by discriminate; destruct four; reflexivity|].
  split; [split; intros; vm_compute; congruence|].
  destruct four.
  - right. rewrite nt_head_threshold_at_witness. discriminate.
  - intros [H|H]; [unfold nt_alias in H; discriminate H|].
    rewrite nt_head_threshold_at_witness in H. exact (H eq_refl).
Qed.
