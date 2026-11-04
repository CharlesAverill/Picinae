(* SSE2 NT head and strategy selection. Original x01 statements: GPT-6 Astra;
   this extension: GPT-6.1 Sol, November 2026.
   Inherited Ubuntu amd64 glibc 2.35-0ubuntu3.12 libc SHA256
   9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
   Unchanged memcpy_amd64 at public entry 0x1c4870, NT head 0x1c4bad.
   System V AMD64: d=RDI, s=RSI, n=RDX, rsp=RSP; RAX=d at cuts.
   This segment copies the first 64 bytes, aligns by a=64-d mod 64, and
   selects the real two/four-page setup. The threshold used for that choice
   is read from the EXACT updated memory, not the initial global. No global
   separation hypothesis, CPU-feature, ordering/cache/fault or termination
   claim is made. PREFETCHT0/NOP, ordinary-store MOVNTDQ and SFENCE projection
   remain inherited unvalidated lifting boundaries. This is IL partial
   correctness of a segment, not the complete strategy. *)
Require Import Picinae_amd64 memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memcpy_proof
  amd64_memcpy_loops_proof amd64_memcpy_nt_proof amd64_memcpy_nt_dispatch_proof.
Import ListNotations.
Open Scope N.

Definition nt_head_memory m d s := nt_row m d s 0.
(* Mask 0xf80 observes only the low twelve bits of the ECX complement. *)
Definition nt_alias d s := (N.lnot (msub 12 s d) 12) .& 0xf80 = 0.
Definition nt_four_selected m d s n :=
  nt_alias d s \/ nt_head_memory m d s Ⓠ[0x3215a8] <= (n-nt_align d) >> 4.
Definition nt_head_input m d s n rsp st :=
  nt_dispatch_state m d s n rsp st /\ st R_RAX=d /\
  xmm_ok st R_YMM0 m s /\ st R_RCX=d ⊖ s.
Definition nt_head_stored m d s n rsp st :=
  st V_MEM64=nt_head_memory m d s /\ st R_RDI=d /\ st R_RSI=s /\
  st R_RDX=n /\ st R_RAX=d /\ st R_RSP=rsp /\ st R_RCX=s ⊖ d.
Definition nt_head_aligned m d s n rsp st :=
  st V_MEM64=nt_head_memory m d s /\ st R_RDI=d+nt_align d /\
  st R_RSI=s ⊕ nt_align d /\ st R_RDX=n-nt_align d /\
  st R_RAX=d /\ st R_RSP=rsp.
Definition nt_head_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1854474 | 1854768 => true | _ => false end | _ => false end.
Definition nt_head_invs m d s n rsp (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1854381 => Some (nt_head_input m d s n rsp st)
  | 1854420 => Some (nt_head_stored m d s n rsp st)
  | 1854454 => Some (nt_head_aligned m d s n rsp st /\ ~nt_alias d s)
  | 1854474 => Some (nt_head_aligned m d s n rsp st /\
                     ~nt_four_selected m d s n /\ st R_R10=(n-nt_align d)>>4)
  | 1854768 => Some (nt_head_aligned m d s n rsp st /\ nt_four_selected m d s n)
  | 1854114 => Some False
  | _ => None end | _ => None end.

Lemma nt_neg_distance: forall d s, msub 64 0 (d ⊖ s)=s ⊖ d.
Proof.
  intros. rewrite msub_msub_distr. rewrite <- add_msub_swap. rewrite N.add_0_l.
  reflexivity.
Qed.

Lemma nt_neg_add: forall d s, (0 ⊖ d) ⊕ s=s ⊖ d.
Proof. intros. rewrite <-add_msub_swap, N.add_0_l. reflexivity. Qed.

Lemma nt_head_copy: forall m d s n,
  64<=n -> nov d s n -> n<2^64 ->
  cpy m (nt_head_memory m d s) d s (fun x => x<64).
Proof.
  intros. eapply cpy_equiv; [|apply (nt_row_advance m m d s n (fun _=>False) 0);
    [apply cpy_empty|intros x []|eassumption|eassumption|assumption]].
  intro x. cbv beta. lia.
Qed.

Lemma nt_head_store_segment: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> 64<=n ->
  nt_head_input m d s n rsp st ->
  nextinv memcpy_amd64 (nt_head_invs m d s n rsp) nt_head_exit false
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

Lemma nt_align_source: forall x d, msub 64 x (msub 64 (d mod 64) 64)=x ⊕ nt_align d.
Proof.
  intros. pose proof (N.mod_lt d 64 ltac:(discriminate)) as DM.
  unfold nt_align, msub.
  rewrite N.mod_mod by discriminate.
  rewrite (N.mod_small 64) by reflexivity.
  rewrite (N.mod_small (d mod 64+(2^64-64))) by (clear - DM; lia).
  f_equal. clear - DM. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma nt_head_align_segment: forall m d s n rsp st t,
  models archtyps st -> d+n<2^64 -> 64<=n -> n<2^64 ->
  nt_head_stored m d s n rsp st ->
  nextinv memcpy_amd64 (nt_head_invs m d s n rsp) nt_head_exit false
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

Lemma nt_head_threshold_segment: forall m d s n rsp st t,
  models archtyps st ->
  nt_head_aligned m d s n rsp st /\ ~nt_alias d s ->
  nextinv memcpy_amd64 (nt_head_invs m d s n rsp) nt_head_exit false
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

Theorem memcpy_nt_head_correct: forall st t st' x' m d s n rsp
  (ENTRY: startof t (x',st')=(Addr 1854381,st))
  (MDL: models x64typctx st) (NOV: nov d s n)
  (NW: d+n<2^64) (BIG: 64<=n) (NB: n<2^64)
  (PRE: nt_head_input m d s n rsp st),
  satisfies_all memcpy_amd64 (nt_head_invs m d s n rsp) nt_head_exit ((x',st')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. exact PRE.
  - intros. erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
    clear - PRE0 MDL1 NOV NW BIG NB. rename t1 into t.
    destruct_inv 64 PRE0.
    + apply nt_head_store_segment; assumption.
    + apply nt_head_align_segment; assumption.
    + apply nt_head_threshold_segment; assumption.
Qed.

(* The bottom-tested loops require a positive count on the selected path.
   This states the exact lower bounds, with no upper-size restriction. *)
Definition nt_strategy_domain m d s n :=
  (nt_four_selected m d s n -> nt_align d+16384<=n) /\
  (~nt_four_selected m d s n -> nt_align d+8192<=n).
Lemma nt_selected_counter_positive: forall m d s n (four:bool),
  nt_strategy_domain m d s n ->
  (if four then nt_four_selected m d s n else ~nt_four_selected m d s n) ->
  0<(n-nt_align d)/(if four then 16384 else 8192).
Proof.
  intros m d s n four [F T] SEL. destruct four.
  - change (0<(n-nt_align d)/(4096*4)). apply nt_chunk_positive; [lia|exact (F SEL)].
  - change (0<(n-nt_align d)/(4096*2)). apply nt_chunk_positive; [lia|exact (T SEL)].
Qed.

