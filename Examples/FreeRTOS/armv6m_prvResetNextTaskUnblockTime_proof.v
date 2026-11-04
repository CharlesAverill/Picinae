(* prvResetNextTaskUnblockTime -- sequential ARMv6-M IL partial correctness.

   Initial author: OpenAI gpt-6-astra, xhigh/default, r26-next-unblock.
   Final proof producer: not certified; see notes/r26-next-unblock/.
   FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0,
   tasks.c:6456-6474, include/list.h:225,258. ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Generated, unchanged finite program: prvResetNextTaskUnblockTime_armv6m.v;
   armv6m_lifter.sh, accepted e05 artifact 95da7ab. Layout evidence:
   Examples/freertos/cortex-m0/evidence/layout.json and nm.txt; config and
   exact source hashes recorded in notes/r26-next-unblock/04-provenance.log.

   AAPCS32: void function, no register arguments or register result. Entry
   0xc6c, common pre-BX cut 0xc7e; nonempty branch 0xc80..0xc8c returns to
   that cut. Immutable code literals supply pxDelayedTaskList=0x20000078
   and xNextTaskUnblockTime=0x20000010. List_t count is at offset 0;
   xListEnd is the 12-byte MiniListItem_t at offset 8; its pxNext at offset
   4 makes the head pointer load list+12. Head xItemValue is at offset 0.
   Four-byte little-endian TickType_t/addresses, modulo 2^32.

   On every executable path to the first BX, exactly four bytes at the
   output global are set to max tick if original count=0, otherwise to the
   value of the original head item. All other bytes equal ORIGINAL memory.
   R0/R1/R4-R12/SP/LR, permissions and temporaries are preserved; only
   R2/R3/NZCV and memory may change. No stack access, callee or oracle.

   The general theorem requires only a typed initial store: arbitrary
   counts, aliasing, modular addresses and head values are allowed; loads
   precede the sole store. Trace execution supplies actual read/write
   permissions. Arbitrary typed-memory witnesses permit all byte accesses.
   The list interpretation is a separate projection of those raw reads:
   it does not assert cardinality, sortedness, or a valid whole kernel.
   The byte frame requires precisely nonoverlap with output[0..4).
   Ordinary BX is actually stepped with odd LR below 0xfffffff0, excluding
   EXC_RETURN. No other CPU/tunable premise. No IRQ/hardware, termination,
   whole-kernel, memory-safety, or validated binary/lifter refinement claim.
 *)
Require Import Picinae_armv6m.
Require Import prvResetNextTaskUnblockTime_armv6m armv6m_list_model.
From Stdlib Require Import NArith Lia List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition next_unblock_list (m:memory) := m Ⓓ[0x20000078].
Definition next_unblock_count (m:memory) := m Ⓓ[next_unblock_list m].
Definition next_unblock_head (m:memory) := m Ⓓ[next_unblock_list m + 12].
Definition next_unblock_result (m:memory) :=
  if next_unblock_count m =? 0 then 0xffffffff
  else m Ⓓ[next_unblock_head m].
Definition next_unblock_memory (m:memory) :=
  setmem 32 LittleE 4 m 0x20000010 (next_unblock_result m).
Definition next_unblock_frame (initial final:store) :=
  forall v, v <> V_MEM32 -> v <> R_R2 -> v <> R_R3 ->
    v <> F_N -> v <> F_Z -> v <> F_C -> v <> F_V ->
    final v = initial v.
Definition next_unblock_postcondition (initial final:store) :=
  final V_MEM32 = next_unblock_memory (initial V_MEM32) /\
  next_unblock_frame initial final.
Definition next_unblock_exit (t:trace) :=
  match t with (Addr 0xc7e,_)::_ => true | _ => false end.
Definition next_unblock_invariants (initial:store) (t:trace) :=
  match t with
  | (Addr 0xc6c,s)::_ => Some (s = initial)
  | (Addr 0xc7e,s)::_ => Some (next_unblock_postcondition initial s)
  | _ => None
  end.

Theorem next_unblock_nwc : forall s2 s1,
  prvResetNextTaskUnblockTime_armv6m_prog s1 =
  prvResetNextTaskUnblockTime_armv6m_prog s2.
Proof. reflexivity. Qed.
Theorem next_unblock_welltyped :
  welltyped_prog armv6mtypctx prvResetNextTaskUnblockTime_armv6m_prog.
Proof. exact prvResetNextTaskUnblockTime_armv6m_welltyped. Qed.

Theorem next_unblock_result_bound : forall m, next_unblock_result m < 2^32.
Proof.
  intro m. unfold next_unblock_result.
  destruct (next_unblock_count m =? 0); [reflexivity|apply getmem_bound].
Qed.

(* Interpret the actual sentinel read, without imposing unrelated list laws. *)
Theorem next_unblock_result_list : forall m p count index,
  next_unblock_list m = p -> list_header m p count index ->
  next_unblock_result m =
    if count =? 0 then list_max_value else field32 m (field32 m p 12) 0.
Proof.
  intros m p count index PTR [COUNT REST].
  unfold next_unblock_result, next_unblock_count, next_unblock_head.
  rewrite PTR.
  unfold field32, list_count_offset in COUNT.
  rewrite N.add_0_r in COUNT. rewrite COUNT.
  unfold field32. rewrite N.add_0_r. reflexivity.
Qed.

Corollary next_unblock_empty_result : forall m p,
  next_unblock_list m = p -> empty_list m p ->
  next_unblock_result m = list_max_value.
Proof.
  intros m p PTR [_ [HEADER _]].
  rewrite (next_unblock_result_list m p 0 (p+8) PTR HEADER). reflexivity.
Qed.

Theorem next_unblock_written_word : forall m,
  getmem 32 LittleE 4 (next_unblock_memory m) 0x20000010 = next_unblock_result m.
Proof.
  intro m. unfold next_unblock_memory.
  rewrite getmem_setmem by discriminate.
  apply N.mod_small, next_unblock_result_bound.
Qed.

Theorem next_unblock_byte_frame : forall m,
  outside_frame32 m (next_unblock_memory m) 0x20000010 4.
Proof. intros m a SEP. unfold next_unblock_memory. apply getmem_noverlap, SEP. Qed.

Theorem next_unblock_written_bytes : forall m i, i < 4 ->
  getmem 32 LittleE 1 (next_unblock_memory m) (0x20000010+i) =
  xbits (next_unblock_result m) (i*8) ((i+1)*8).
Proof.
  intros m i B. unfold next_unblock_memory.
  replace 4 with (i+1+(3-i)) at 1 by (clear - B; lia).
  apply getmem_setmem_xbits. clear - B. lia.
Qed.

Definition next_unblock_entry_witness (m:memory) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ | A_WRITE => N.ones (2^32)
  | R_LR => 1
  | _ => 0
  end.
Definition next_unblock_permitted (s:store) :=
  forall a, a < 2^32 -> mem_readable s a /\ mem_writable s a.

Lemma next_unblock_witness_models : forall m,
  m < 2^(8*2^32) -> models armv6mtypctx (next_unblock_entry_witness m).
Proof.
  intros m B v w T. destruct v; cbn [armv6mtypctx] in T;
    try discriminate; injection T as <-.
  all: lazymatch goal with
  | |- next_unblock_entry_witness _ V_MEM32 < _ => exact B
  | |- next_unblock_entry_witness _ A_READ < _ => exact (ones_bound (2^32))
  | |- next_unblock_entry_witness _ A_WRITE < _ => exact (ones_bound (2^32))
  | |- next_unblock_entry_witness _ R_LR < _ => change (1 < 2^32); reflexivity
  | |- _ < 2^?width => exact (mp2_gt_0 width)
  end.
Qed.

Theorem next_unblock_entry_satisfiable : forall m,
  m < 2^(8*2^32) ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\
    next_unblock_permitted s /\ N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.
Proof.
  intros m B. exists (next_unblock_entry_witness m).
  split; [apply next_unblock_witness_models, B|].
  split; [reflexivity|]. split.
  - intros a A. unfold mem_readable, mem_writable.
    change (N.testbit (N.ones (2^32)) a = true /\
            N.testbit (N.ones (2^32)) a = true).
    split; apply N.ones_spec_low; exact A.
  - split; reflexivity.
Qed.

Theorem next_unblock_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0xc6c,s))
  (MDL: models armv6mtypctx s),
  satisfies_all prvResetNextTaskUnblockTime_armv6m_prog
    (next_unblock_invariants s) next_unblock_exit ((x',s')::t).
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.

Corollary next_unblock_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0xc7e,s') = (Addr 0xc6c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog prvResetNextTaskUnblockTime_armv6m_prog ((Addr 0xc7e,s')::t))
  (UT: unterminated next_unblock_exit t),
  next_unblock_postcondition s s'.
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.

Corollary next_unblock_original_memory_effect : forall s t s'
  (ENTRY: startof t (Addr 0xc7e,s') = (Addr 0xc6c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog prvResetNextTaskUnblockTime_armv6m_prog ((Addr 0xc7e,s')::t))
  (UT: unterminated next_unblock_exit t),
  getmem 32 LittleE 4 (s' V_MEM32) 0x20000010 = next_unblock_result (s V_MEM32) /\
  outside_frame32 (s V_MEM32) (s' V_MEM32) 0x20000010 4 /\
  (forall i, i < 4 -> getmem 32 LittleE 1 (s' V_MEM32) (0x20000010+i) =
     xbits (next_unblock_result (s V_MEM32)) (i*8) ((i+1)*8)).
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.

Corollary next_unblock_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0xc7e,s') = (Addr 0xc6c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog prvResetNextTaskUnblockTime_armv6m_prog ((Addr 0xc7e,s')::t))
  (UT: unterminated next_unblock_exit t),
  forall v, In v [R_R0; R_R1; R_R4; R_R5; R_R6; R_R7; R_R8;
    R_R9; R_R10; R_R11; R_R12; R_SP; R_LR; A_READ; A_WRITE; A_EXEC] -> s' v = s v.
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.

Theorem next_unblock_return_step : forall s
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  can_step prvResetNextTaskUnblockTime_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0xc7e,s)).
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.

Corollary next_unblock_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0xc7e,s') = (Addr 0xc6c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog prvResetNextTaskUnblockTime_armv6m_prog ((Addr 0xc7e,s')::t))
  (UT: unterminated next_unblock_exit t)
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  next_unblock_postcondition s s' /\
  can_step prvResetNextTaskUnblockTime_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0xc7e,s')).
(* WIP: unverified repair is archived in notes/r26-next-unblock-fix/. *)
Abort.
