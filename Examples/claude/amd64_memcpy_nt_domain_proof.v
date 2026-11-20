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

Require Import amd64_memcpy_nt_head_proof.

Lemma nt_head_threshold_at_witness: forall threshold,
  nt_head_memory (0 [Ⓠ 0x3215a8 := threshold]) 65536 131072 Ⓠ[0x3215a8]
    = threshold mod 2^64.
Proof.
  intro threshold. unfold nt_head_memory, nt_row.
  repeat rewrite getmem_frame by (left; vm_compute; discriminate).
  rewrite getmem_setmem by discriminate. reflexivity.
Qed.

Theorem nt_strategy_domain_nonvacuous: forall (four:bool),
  exists m d s n,
    nov d s n /\ d+n<2^64 /\ n<2^64 /\ 128<n /\
    m Ⓠ[0x3215a8]<n /\ nt_strategy_domain m d s n /\
    (if four then nt_four_selected m d s n else ~nt_four_selected m d s n).
Proof.
  intro four.
  assert (NOV: nov 65536 131072 16448).
  { intros i j I J. rewrite !N.mod_small by (clear - I J; lia).
    clear - I J; lia. }
  destruct four.
  - exists (0 [Ⓠ 0x3215a8 := 0]), 65536, 131072, 16448.
    split; [exact NOV|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [rewrite getmem_setmem by discriminate; reflexivity|].
    split; [split; intros; vm_compute; congruence|].
    right. rewrite nt_head_threshold_at_witness. discriminate.
  - exists (0 [Ⓠ 0x3215a8 := 4096]), 65536, 131072, 16448.
    split; [exact NOV|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [rewrite getmem_setmem by discriminate; reflexivity|].
    split; [split; intros; vm_compute; congruence|].
    intros [H|H].
    + unfold nt_alias in H. discriminate H.
    + rewrite nt_head_threshold_at_witness in H. exact (H eq_refl).
Qed.

Lemma nt_zero_load: forall len a, getmem 64 LittleE len 0 a=0.
Proof.
  intros. apply N.bits_inj. intro i.
  rewrite getmem_spec, !N.bits_0, Bool.andb_false_r. reflexivity.
Qed.
Definition nt_head_witness threshold : store := fun v => match v with
  | R_RDI | R_RAX => 65536 | R_RSI => 131072 | R_RDX => 16448
  | R_RCX => 65536 ⊖ 131072
  | V_MEM64 => 0 [Ⓠ 0x3215a8 := threshold]
  | _ => 0 end.
Theorem memcpy_nt_head_nonvacuous: forall threshold,
  models x64typctx (nt_head_witness threshold) /\
  nt_head_input (0 [Ⓠ 0x3215a8 := threshold]) 65536 131072 16448 0
    (nt_head_witness threshold) /\
  nov 65536 131072 16448 /\ 65536+16448<2^64 /\
  64<=16448 /\ 16448<2^64.
Proof.
  intro threshold. split.
  { intros v w T. destruct v; inversion T; subst;
      cbv [nt_head_witness]; try first
        [apply N.neq_0_lt_0; apply N.pow_nonzero; discriminate|apply msub_lt|reflexivity|discriminate
        |apply typesafe_setmem; apply N.neq_0_lt_0; apply N.pow_nonzero; discriminate].
    change ((0 [Ⓠ0x3215a8 := threshold]) < memsize 64).
    apply typesafe_setmem.
    Transparent memsize.
    unfold memsize. apply N.neq_0_lt_0. apply N.pow_nonzero. discriminate.
    Opaque memsize. }
  split.
  { unfold nt_head_input, nt_dispatch_state. split;
      [repeat split; reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    unfold xmm_ok. change (0=(0 [Ⓠ 0x3215a8 := threshold]) Ⓧ[131072]).
    rewrite getmem_frame by (left; vm_compute; discriminate). symmetry. apply nt_zero_load. }
  split.
  { intros i j I J. rewrite !N.mod_small by (clear - I J; lia).
    clear - I J; lia. }
  repeat split; first [reflexivity|discriminate].
Qed.

Require Import amd64_memcpy_nt_bulk_proof.

Lemma nt_head_memory_bound: forall m d s,
  m<memsize 64 -> nt_head_memory m d s<memsize 64.
Proof.
  intros. unfold nt_head_memory, nt_row.
  repeat apply typesafe_setmem. assumption.
Qed.
Lemma nt_zero_memory_bound: 0<memsize 64.
Proof.
  Transparent memsize.
  unfold memsize. apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
Qed.
Opaque memsize.

Definition nt_bulk_witness (four:bool) : store := fun v => match v with
 | R_RDI => 65600 | R_RSI => 131136 | R_RCX => 64
 | R_R10 => if four then 1 else 2 | R_RAX => 65536
 | V_MEM64 => nt_head_memory 0 65536 131072 | _ => 0 end.
Theorem memcpy_nt_bulk_nonvacuous: forall four,
  models x64typctx (nt_bulk_witness four) /\
  nov 65536 131072 16448 /\ 65536+16448<2^64 /\
  16448<2^64 /\ 64<=16448 /\
  nt_bulk_state four 0 65536 131072 16448 0 0 0 (nt_bulk_witness four).
Proof.
  intro four.
  assert (NOV: nov 65536 131072 16448).
  { intros i j I J. rewrite !N.mod_small by (clear - I J; lia).
    clear - I J; lia. }
  split.
  { intros v w T. destruct v; inversion T; subst;
      cbv [nt_bulk_witness];
      lazymatch goal with
      | |- nt_head_memory _ _ _ < _ =>
          change (nt_head_memory 0 65536 131072<memsize 64);
          apply nt_head_memory_bound, nt_zero_memory_bound
      | |- _ => first
          [apply N.neq_0_lt_0; apply N.pow_nonzero; discriminate
          |destruct four; reflexivity]
      end. }
  split; [exact NOV|]. split; [reflexivity|]. split; [reflexivity|].
  split; [discriminate|].
  unfold nt_bulk_state. split; [destruct four; reflexivity|].
  split; [reflexivity|]. split.
  { change (cpy 0 (nt_head_memory 0 65536 131072) 65536 131072
      (nt_done (nt_pages four) (nt_align 65536) 0 0)).
    eapply cpy_equiv; [|apply (nt_head_copy 0 65536 131072 16448);
      first [exact NOV|reflexivity|discriminate]].
    intro x. symmetry. apply nt_done_initial. }
  repeat split; destruct four; reflexivity.
Qed.
