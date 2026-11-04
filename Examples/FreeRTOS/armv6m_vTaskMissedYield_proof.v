(* PARTIAL: initial full build exceeded the assigned memory cap.
   All 18 initial proof attempts are archived verbatim in
   notes/r11-missed-yield/initial-attempt.v.txt. Statements below are
   deliberately aborted, not certified. No Astra repair cycle was run. *)

(* vTaskMissedYield -- set the actual yield-pending word, sequential ARMv6-M IL.

   Initial author: OpenAI gpt-6-astra, xhigh, default, one-shot (r11-missed-yield).
   Validation and final proof producer: see notes/r11-missed-yield/README.md.
   FreeRTOS V11.1.0 commit dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Generated vTaskMissedYield_armv6m.v (armv6m_lifter.sh) is unchanged.
   Evidence: vTaskMissedYield.json, abi.json, and ../freertos/cortex-m0/
   {inputs.json,FreeRTOSConfig.h,evidence/layout.json,evidence/manifest.json}.
   configNUMBER_OF_CORES=1; BaseType_t is four bytes; xYieldPendings[0]
   is at object offset zero, address 0x2000001c, object size four bytes.

   AAPCS32 void function, no register arguments. Entry 0x9c0 loads R3 from
   the immutable literal at 0x9c8; 0x9c2 sets R2=1, N=Z=0; 0x9c4 stores
   four little-endian bytes at 0x2000001c; exit cut 0x9c6 is BX LR.
   The postcondition gives the exact memory update relative to ENTRY memory,
   word=1, bytes=[1;0;0;0], and preserves every other byte modulo 2^32.
   All variables except V_MEM32/R2/R3/N/Z are preserved, including R0/R1,
   R4-R12, SP/LR, C/V, permissions, and temporaries. No stack access occurs.

   Exact-state partial correctness assumes only a typed entry store and an
   actual finite-map execution to the first exit cut. A permitted entry
   additionally grants write permission on these four bytes and ordinary LR:
   odd and strictly below 0xfffffff0. Arbitrary typed original-memory and LR
   witnesses are supplied, as are actual instruction/finite-trace witnesses.
   No old pending-value, path, size, overlap, CPU-feature or tunable restriction
   is imposed. The fixed address is aligned and nonwrapping; no callee oracle.
   Return is the actual guarded ordinary BX step, with the low LR bit cleared.
   This is not hardware EXC_RETURN, IRQ/concurrency, whole-kernel correctness,
   scheduler cardinality, a termination theorem, or binary/lifter refinement.
   The inherited decoder and immutable literal-folding provenance are trusted.
 *)

Require Import Picinae_armv6m vTaskMissedYield_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition missed_yield_memory (s:store) : memory :=
  (s V_MEM32) [Ⓓ 0x2000001c := 1].
Definition missed_yield_register_frame (s0 s:store) : Prop :=
  forall v, v <> V_MEM32 -> v <> R_R2 -> v <> R_R3 ->
    v <> F_N -> v <> F_Z -> s v = s0 v.
Definition missed_yield_postcondition (s0 s:store) : Prop :=
  s V_MEM32 = missed_yield_memory s0 /\ s R_R2 = 1 /\
  s R_R3 = 0x2000001c /\ s F_N = 0 /\ s F_Z = 0 /\
  missed_yield_register_frame s0 s.
Definition missed_yield_byte_frame (s0 s:store) : Prop :=
  forall a, ~ overlap 32 a 1 0x2000001c 4 ->
    (s V_MEM32) Ⓑ[a] = (s0 V_MEM32) Ⓑ[a].
Definition missed_yield_exit (t:trace) : bool :=
  match t with (Addr 0x9c6,_)::_ => true | _ => false end.
Definition missed_yield_invariants (s0:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x9c0,s)::_ => Some (s = s0)
  | (Addr 0x9c6,s)::_ => Some (missed_yield_postcondition s0 s)
  | _ => None end.
Definition missed_yield_writable (s:store) : Prop :=
  forall i, i < 4 -> mem_writable s ((0x2000001c+i) mod 2^32).
Definition missed_yield_ordinary_lr (lr:N) : Prop :=
  lr < 0xfffffff0 /\ N.odd lr = true.
Definition missed_yield_entry (s:store) : Prop :=
  models armv6mtypctx s /\ missed_yield_writable s /\
  missed_yield_ordinary_lr (s R_LR).

Theorem missed_yield_welltyped :
  welltyped_prog armv6mtypctx vTaskMissedYield_armv6m_prog.
Proof. Abort.
Theorem missed_yield_nwc : forall s1 s2,
  vTaskMissedYield_armv6m_prog s1 = vTaskMissedYield_armv6m_prog s2.
Proof. Abort.

Theorem missed_yield_memory_word : forall s,
  (missed_yield_memory s) Ⓓ[0x2000001c] = 1.
Proof. Abort.
Theorem missed_yield_memory_bytes : forall s,
  (missed_yield_memory s) Ⓑ[0x2000001c] = 1 /\
  (missed_yield_memory s) Ⓑ[0x2000001d] = 0 /\
  (missed_yield_memory s) Ⓑ[0x2000001e] = 0 /\
  (missed_yield_memory s) Ⓑ[0x2000001f] = 0.
Proof. Abort.
Theorem missed_yield_memory_outside : forall s a,
  ~ overlap 32 a 1 0x2000001c 4 ->
  (missed_yield_memory s) Ⓑ[a] = (s V_MEM32) Ⓑ[a].
Proof. Abort.

Theorem missed_yield_preserves_registers : forall v,
  v <> V_MEM32 -> v <> R_R2 -> v <> R_R3 -> v <> F_N -> v <> F_Z ->
  forall_endstates vTaskMissedYield_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof. Abort.

Theorem missed_yield_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s),
  satisfies_all vTaskMissedYield_armv6m_prog
    (missed_yield_invariants s) missed_yield_exit ((x',s')::t).
Proof. Abort.

Corollary missed_yield_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x9c6,s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog vTaskMissedYield_armv6m_prog ((Addr 0x9c6,s')::t))
  (UT: unterminated missed_yield_exit t),
  missed_yield_postcondition s s'.
Proof. Abort.

Corollary missed_yield_functional : forall s t s'
  (ENTRY: startof t (Addr 0x9c6,s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog vTaskMissedYield_armv6m_prog ((Addr 0x9c6,s')::t))
  (UT: unterminated missed_yield_exit t),
  (s' V_MEM32) Ⓓ[0x2000001c] = 1 /\
  ((s' V_MEM32) Ⓑ[0x2000001c] = 1 /\
   (s' V_MEM32) Ⓑ[0x2000001d] = 0 /\
   (s' V_MEM32) Ⓑ[0x2000001e] = 0 /\
   (s' V_MEM32) Ⓑ[0x2000001f] = 0) /\
  missed_yield_byte_frame s s'.
Proof. Abort.
Corollary missed_yield_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x9c6,s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog vTaskMissedYield_armv6m_prog ((Addr 0x9c6,s')::t))
  (UT: unterminated missed_yield_exit t),
  forall v, In v [R_R4;R_R5;R_R6;R_R7;R_R8;R_R9;R_R10;R_R11;R_SP;R_LR] ->
    s' v = s v.
Proof. Abort.

Lemma missed_yield_zero_bound : forall w, 0 < 2^w.
Proof. Abort.
Definition missed_yield_entry_store (m lr:N) : store := fun v =>
  match v with V_MEM32 => m | A_WRITE => N.ones (2^32) | R_LR => lr | _ => 0 end.
Theorem missed_yield_entry_satisfiable : forall m lr,
  m < 2^(8*2^32) -> missed_yield_ordinary_lr lr ->
  exists s, missed_yield_entry s /\ s V_MEM32 = m /\ s R_LR = lr.
Proof. Abort.

Definition missed_yield_after_ldr (s:store) := reset_temps s (update s R_R3 0x2000001c).
Definition missed_yield_after_mov (s:store) :=
  let sl := missed_yield_after_ldr s in
  reset_temps sl (update (update (update sl F_N 0) F_Z 0) R_R2 1).
Definition missed_yield_after_store (s:store) :=
  let sm := missed_yield_after_mov s in
  reset_temps sm (update sm V_MEM32 (missed_yield_memory s)).

Theorem missed_yield_ldr_step : forall s,
  can_step vTaskMissedYield_armv6m_prog
    ((Addr 0x9c2,missed_yield_after_ldr s),(Addr 0x9c0,s)).
Proof. Abort.
Theorem missed_yield_mov_step : forall s,
  can_step vTaskMissedYield_armv6m_prog
    ((Addr 0x9c4,missed_yield_after_mov s),(Addr 0x9c2,missed_yield_after_ldr s)).
Proof. Abort.
Theorem missed_yield_store_step : forall s, missed_yield_writable s ->
  can_step vTaskMissedYield_armv6m_prog
    ((Addr 0x9c6,missed_yield_after_store s),(Addr 0x9c4,missed_yield_after_mov s)).
Proof. Abort.
Theorem missed_yield_execution_witness : forall s, missed_yield_entry s ->
  exec_prog vTaskMissedYield_armv6m_prog
    [(Addr 0x9c6,missed_yield_after_store s); (Addr 0x9c4,missed_yield_after_mov s);
     (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)] /\
  missed_yield_postcondition s (missed_yield_after_store s).
Proof. Abort.

Theorem missed_yield_return_step : forall s,
  missed_yield_ordinary_lr (s R_LR) ->
  can_step vTaskMissedYield_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32-1)),s),(Addr 0x9c6,s)).
Proof. Abort.
Corollary missed_yield_execution_returns : forall s, missed_yield_entry s ->
  exec_prog vTaskMissedYield_armv6m_prog
    [(Addr (N.land (s R_LR) (N.ones 32-1)),missed_yield_after_store s);
     (Addr 0x9c6,missed_yield_after_store s); (Addr 0x9c4,missed_yield_after_mov s);
     (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)].
Proof. Abort.
