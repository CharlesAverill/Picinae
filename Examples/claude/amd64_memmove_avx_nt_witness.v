(* Nonvacuity witness for the original AVX NT public input contract.
   OpenAI GPT-6.1 Sol, x02-avx-nt-fix, 2026-11-03.
   Sequential IL input witness only; no execution/termination claim. *)
Require Import Picinae_amd64.
Require Import amd64_memcpy_sets.
Require Import amd64_memmove_avx_nt_proof.
From Stdlib Require Import NArith Lia.
Open Scope N.

(* Keep the address symbolic, so reduction never constructs an enormous
   power of two merely to read a zero byte at a large concrete address. *)
Lemma nt_zero_memory_load: forall w e len a, getmem w e len 0 a = 0.
Proof.
  intros w e len. induction len using N.peano_ind; intro a.
  - apply getmem_0.
  - rewrite getmem_succ. destruct e; rewrite IHlen;
      unfold getbyte; rewrite xbits_0_l; apply cbits_0_l.
Qed.

(* A concrete modeled entry satisfies every public precondition. Zero initial
   memory makes both tunables zero; the two 32768-byte buffers are disjoint.
   This witnesses inputs, not termination or a caller-return execution. *)
Definition nt_entry_witness : store := fun v =>
  match v with
  | R_RDI => 65536
  | R_RSI => 131072
  | R_RDX => 32768
  | _ => 0
  end.

Lemma nt_entry_inputs_satisfiable:
  models x64typctx nt_entry_witness /\
  nt_entry_witness V_MEM64 = 0 /\
  nt_entry_witness R_RDI = 65536 /\
  nt_entry_witness R_RSI = 131072 /\
  nt_entry_witness R_RDX = 32768 /\
  nt_entry_witness R_RSP = 0 /\
  nov 65536 131072 32768 /\
  65536 + 32768 < 2^64 /\ 131072 + 32768 <= 2^64 /\
  16448 <= 32768 /\
  getmem 64 LittleE 8 0 0x31a3f8 < 32768 /\
  getmem 64 LittleE 8 0 0x3215a0 <= 32768.
Proof.
  split.
  { intros v w T. destruct v; cbv [nt_entry_witness];
      try (apply N.neq_0_lt_0, N.pow_nonzero; discriminate).
    all: change (Some 64 = Some w) in T; injection T as <-;
      change (2^64) with 18446744073709551616; lia. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros i j I J.
    rewrite !N.mod_small by (change (2^64) with 18446744073709551616; lia).
    lia. }
  change (2^64) with 18446744073709551616.
  rewrite !nt_zero_memory_load.
  repeat split; lia.
Qed.
