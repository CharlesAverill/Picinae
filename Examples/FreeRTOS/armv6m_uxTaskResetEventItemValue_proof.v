(* PARTIAL: initial full build exhausted the assigned memory cap.
   Every theorem attempt below is aborted, not exported. Exact initial proofs:
   notes/r13-reset-event/initial-attempt.v.txt. No Astra repair cycle was run. *)

(* uxTaskResetEventItemValue -- ARMv6-M Cortex-M0 sequential IL contract.

   Initial author: OpenAI gpt-6-astra, xhigh/default, unit r13-reset-event.
   Final proof producer: pending full kernel validation; see notes/r13-reset-event.
   Provenance: FreeRTOS Kernel V11.1.0, commit
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0, tasks.c lines 7569-7584,
   SHA256 6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149.
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Generated unchanged map: uxTaskResetEventItemValue_armv6m.v, strict
   armv6m_lifter.sh; accepted e05 leaf artifact, no calls/closure premises.
   Evidence: uxTaskResetEventItemValue.json and ../freertos/cortex-m0/
   evidence/layout.json, evidence/manifest.json, FreeRTOSConfig.h.

   ABI/spec: no register arguments; entry 0x1524; BX LR cut 0x1536.
   The immutable literal at 0x1538 supplies pxCurrentTCB's address 0x20000108.
   INITIAL memory supplies that pointer, the original 32-bit little-endian
   event value at TCB+24 (xEventListItem+0), and priority at TCB+44.
   configMAX_PRIORITIES=5. Return the original event value in R0 and write
   (5-priority) modulo 2^32 to precisely the four event-value bytes.
   R0-R3, NZCV and those four bytes may change. All other variables agree,
   including R4-R11, R12, SP, LR, permissions, and temporaries.
   Both pointer arithmetic and the four-byte memory access wrap modulo 2^32.
   No pointer alignment, non-overlap, priority-range, CPU-feature or tunable
   hypothesis is needed for this IL contract. Even aliases are allowed:
   reads precede the only store, and the memory frame excludes exactly that
   store footprint. This does not assert preservation of aliased objects.
   Ordinary priorities <5 additionally give the natural value 5-priority.

   The main invariant theorem assumes a typed entry store. Actual executable
   traces supply read/write permissions. A separate arbitrary-memory/ordinary-LR
   witness proves these permissions and typing are jointly satisfiable.
   The ordinary BX step is proved only for odd LR below 0xfffffff0; it clears
   bit zero and leaves the entire store unchanged. No callee oracle, IRQ,
   hardware/exception behavior, scheduler invariant, whole-kernel correctness,
   termination or proved binary/lifter refinement is claimed. Literal folding
   and the inherited unvalidated lift remain in the trusted provenance boundary.
 *)

Require Import Picinae_armv6m.
Require Import uxTaskResetEventItemValue_armv6m.
From Stdlib Require Import NArith List Lia FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition reset_event_tcb (m:memory) : N := m Ⓓ[0x20000108].
Definition reset_event_address (m:memory) : N := reset_event_tcb m ⊕ 24.
Definition reset_event_original (m:memory) : N := m Ⓓ[reset_event_address m].
Definition reset_event_priority (m:memory) : N := m Ⓓ[reset_event_tcb m ⊕ 44].
Definition reset_event_value (m:memory) : N := 5 ⊖ reset_event_priority m.
Definition reset_event_memory (m:memory) : memory :=
  m [Ⓓ reset_event_address m := reset_event_value m].

Definition reset_event_frame (initial final:store) : Prop :=
  forall v, ~ In v [V_MEM32; R_R0; R_R1; R_R2; R_R3; F_N; F_Z; F_C; F_V] ->
    final v = initial v.
Definition reset_event_postcondition (initial final:store) : Prop :=
  final R_R0 = reset_event_original (initial V_MEM32) /\
  final V_MEM32 = reset_event_memory (initial V_MEM32) /\
  reset_event_frame initial final.
Definition reset_event_exit (t:trace) : bool :=
  match t with (Addr 0x1536,_)::_ => true | _ => false end.
Definition reset_event_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x1524,s)::_ => Some (s = initial)
  | (Addr 0x1536,s)::_ => Some (reset_event_postcondition initial s)
  | _ => None
  end.
Definition reset_event_permitted (s:store) : Prop :=
  forall i, i < 4 ->
    mem_readable s (0x20000108 ⊕ i) /\
    mem_readable s (reset_event_address (s V_MEM32) ⊕ i) /\
    mem_readable s ((reset_event_tcb (s V_MEM32) ⊕ 44) ⊕ i) /\
    mem_writable s (reset_event_address (s V_MEM32) ⊕ i).

Theorem reset_event_nwc : forall s2 s1,
  uxTaskResetEventItemValue_armv6m_prog s1 = uxTaskResetEventItemValue_armv6m_prog s2.
Abort.
Theorem reset_event_welltyped :
  welltyped_prog armv6mtypctx uxTaskResetEventItemValue_armv6m_prog.
Abort.

Lemma reset_event_zero_bound : forall w, 0 < 2^w.
Abort.
Definition reset_event_entry_witness (m:memory) (lr:N) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ | A_WRITE => N.ones (2^32)
  | R_LR => lr
  | _ => 0
  end.
Lemma reset_event_witness_models : forall m lr,
  m < 2^(8*2^32) -> lr < 2^32 ->
  models armv6mtypctx (reset_event_entry_witness m lr).
Abort.
Theorem reset_event_entry_satisfiable : forall m lr,
  m < 2^(8*2^32) -> N.odd lr = true -> lr < 0xfffffff0 ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\ s R_LR = lr /\
    reset_event_permitted s /\ N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.
Abort.

(* Flags are intentionally unconstrained in the postcondition. *)
Ltac ignore_vars v ::= constr:(match v with F_N | F_Z | F_C | F_V => true | _ => false end).

Theorem reset_event_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x1524,s))
  (MDL: models armv6mtypctx s),
  satisfies_all uxTaskResetEventItemValue_armv6m_prog
    (reset_event_invariants s) reset_event_exit ((x',s')::t).
Abort.

Corollary reset_event_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x1536,s') = (Addr 0x1524,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskResetEventItemValue_armv6m_prog ((Addr 0x1536,s')::t))
  (UT: unterminated reset_event_exit t),
  reset_event_postcondition s s'.
Abort.

Corollary reset_event_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x1536,s') = (Addr 0x1524,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskResetEventItemValue_armv6m_prog ((Addr 0x1536,s')::t))
  (UT: unterminated reset_event_exit t),
  forall v, In v [R_R4; R_R5; R_R6; R_R7; R_R8; R_R9; R_R10; R_R11; R_R12; R_SP; R_LR] ->
    s' v = s v.
Abort.

Theorem reset_event_stored_word : forall m,
  (reset_event_memory m) Ⓓ[reset_event_address m] = reset_event_value m.
Abort.
Theorem reset_event_written_byte : forall m i, i < 4 ->
  getbyte (reset_event_memory m) (reset_event_address m + i) 32 =
    N.shiftr (reset_event_value m) (i*8) mod 256.
Abort.
Theorem reset_event_memory_frame : forall m a,
  4 <= msub 32 a (reset_event_address m) ->
  getbyte (reset_event_memory m) a 32 = getbyte m a 32.
Abort.
Theorem reset_event_priority_normal : forall m, reset_event_priority m < 5 ->
  reset_event_value m = 5 - reset_event_priority m.
Abort.

Corollary reset_event_original_memory_effects : forall s t s'
  (ENTRY: startof t (Addr 0x1536,s') = (Addr 0x1524,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskResetEventItemValue_armv6m_prog ((Addr 0x1536,s')::t))
  (UT: unterminated reset_event_exit t),
  s' R_R0 = reset_event_original (s V_MEM32) /\
  (s' V_MEM32) Ⓓ[reset_event_address (s V_MEM32)] = reset_event_value (s V_MEM32) /\
  (forall i, i < 4 -> getbyte (s' V_MEM32) (reset_event_address (s V_MEM32)+i) 32 =
    N.shiftr (reset_event_value (s V_MEM32)) (i*8) mod 256) /\
  (forall a, 4 <= msub 32 a (reset_event_address (s V_MEM32)) ->
    getbyte (s' V_MEM32) a 32 = getbyte (s V_MEM32) a 32).
Abort.

Theorem reset_event_return_step : forall s
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  can_step uxTaskResetEventItemValue_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x1536,s)).
Abort.

Corollary reset_event_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x1536,s') = (Addr 0x1524,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskResetEventItemValue_armv6m_prog ((Addr 0x1536,s')::t))
  (UT: unterminated reset_event_exit t)
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  reset_event_postcondition s s' /\
  can_step uxTaskResetEventItemValue_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0x1536,s')).
Abort.
