(* SSE2 NT bulk-loop extension, GPT-6.1 Sol, November 2026.
   Same inherited glibc/lifter provenance and projection boundaries as
   amd64_memcpy_nt_head_proof. This file concerns the unchanged actual
   64-iteration two/four-page loops, not the AVX 32-iteration body. *)
Require Import Picinae_amd64 memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memcpy_proof
  amd64_memcpy_loops_proof amd64_memcpy_nt_proof.
Import ListNotations.
Open Scope N.

Require Import amd64_memcpy_nt_bulk_proof.

Lemma nt_bulk_iteration4: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> d+n<2^64 -> n<2^64 -> 64<=n ->
  (exists j i, nt_bulk_state true m d s n rsp j i st) ->
  nextinv memcpy_amd64 (nt_bulk_invs true m d s n rsp) (nt_bulk_exit true) false
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

(* This theorem starts at a real inner-loop cut with the counter relation
   explicit. It is not a public-entry strategy theorem: setup and joins must
   still connect these premises to the head and the final tails. *)
Theorem memcpy_nt_bulk_from_inner_correct:
  forall (four:bool) st t st' x' m d s n rsp
    (ENTRY: startof t (x',st')=(Addr (if four then 1854789 else 1854501),st))
    (MDL: models x64typctx st) (NOV: nov d s n)
    (NW: d+n<2^64) (NB: n<2^64) (BIG: 64<=n)
    (PRE: exists j i, nt_bulk_state four m d s n rsp j i st),
  satisfies_all memcpy_amd64 (nt_bulk_invs four m d s n rsp)
    (nt_bulk_exit four) ((x',st')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. destruct four; x64_step; exact PRE.
  - intros. erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
    clear - PRE0 MDL1 NOV NW NB BIG. rename t1 into t.
    destruct four; destruct_inv 64 PRE0;
      first [apply nt_bulk_iteration2; assumption|apply nt_bulk_iteration4; assumption].
Qed.
