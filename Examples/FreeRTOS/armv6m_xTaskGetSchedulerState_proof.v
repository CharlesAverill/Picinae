(* xTaskGetSchedulerState -- ARMv6-M Cortex-M0 sequential IL correctness.

   Initial author: OpenAI gpt-6-astra, xhigh/default, r19-scheduler-state.
   Repair: OpenAI gpt-6.1-sol, xhigh/default, r19-scheduler-state-fix.
   PARTIAL: seven helpers checked in diagnostic compilation; main proof unfinished.
   Original evidence: notes/r19-scheduler-state; repairs: notes/r19-scheduler-state-fix.
   FreeRTOS V11.1.0, commit dbf70559b27d39c1fdb68dfb9a32140b6a6777a0.
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Lift: unchanged xTaskGetSchedulerState_armv6m.v, armv6m_lifter.sh;
   accepted call-free e05 artifact at 95da7ab7cee78f09a528aed86c1dfaf29520a9a8.
   Source: pinned tasks.c:6540-6573, task.h:276-278, projdefs.h:52.
   Config/layout: Examples/freertos/cortex-m0/{FreeRTOSConfig.h,evidence/};
   configNUMBER_OF_CORES=1, INCLUDE_xTaskGetSchedulerState=1;
   sizeof(BaseType_t)=sizeof(UBaseType_t)=sizeof(pointer)=4.
   Manifest xTaskGetSchedulerState.json and nm.txt identify two scalar objects,
   each offset zero and size four: xSchedulerRunning at 0x20000024 and
   uxSchedulerSuspended at 0x20000008. Literal pools 0x1314/0x1318 are folded
   immutable code, not mutable-memory assumptions. See 06-evidence.log.

   English/ABI spec: no arguments; at entry 0x12fc, use INITIAL memory words.
   R0 at the first BX LR (0x1310) is NOT_STARTED=1 if running=0; otherwise
   RUNNING=2 if suspended=0, SUSPENDED=0 otherwise. All 32-bit word values
   are covered, without Boolean-only or reachable-kernel-state assumptions.
   No bytes are written. Every variable except R0/R3/N/Z/C/V is preserved,
   including memory, R4-R11, SP, LR, permissions and original temporaries.
   No intermediate invariant cuts: entry 0x12fc and sole exit 0x1310.
   Running=0 takes the BEQ at 0x1304; the other path executes the real
   NEG/ADC/LSL sequence at 0x130a/0x130c/0x130e.

   Preconditions: models armv6mtypctx for functional partial correctness;
   actual exec_prog traces supply memory-read permission premises. The
   explicit entry witness permits all eight global bytes for arbitrary
   bounded modeled memory. There are no pointer input, size, overlap, CPU
   feature or tunable restrictions beyond this pinned 32-bit sequential IL.
   The separate actual BX step additionally requires odd LR < 0xfffffff0,
   excluding architectural exception-return encodings; it clears bit zero.
   No callee oracle, IRQ/hardware/whole-kernel/cardinality/termination claim,
   or proof of binary-to-IL refinement is made.
 *)
Require Import Picinae_armv6m.
Require Import xTaskGetSchedulerState_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition scheduler_state_result (m:memory) : N :=
  if m Ⓓ[0x20000024] =? 0 then 1
  else if m Ⓓ[0x20000008] =? 0 then 2 else 0.

Definition scheduler_state_frame (initial final:store) : Prop :=
  forall v, v <> R_R0 -> v <> R_R3 ->
    v <> F_N -> v <> F_Z -> v <> F_C -> v <> F_V ->
    final v = initial v.

Definition scheduler_state_postcondition (initial final:store) : Prop :=
  final R_R0 = scheduler_state_result (initial V_MEM32) /\
  scheduler_state_frame initial final.

Definition scheduler_state_exit (t:trace) : bool :=
  match t with (Addr 0x1310,_)::_ => true | _ => false end.

Definition scheduler_state_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x12fc,s)::_ => Some (s = initial)
  | (Addr 0x1310,s)::_ => Some (scheduler_state_postcondition initial s)
  | _ => None
  end.

Theorem scheduler_state_nwc : forall s2 s1,
  xTaskGetSchedulerState_armv6m_prog s1 = xTaskGetSchedulerState_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem scheduler_state_welltyped :
  welltyped_prog armv6mtypctx xTaskGetSchedulerState_armv6m_prog.
Proof. exact xTaskGetSchedulerState_armv6m_welltyped. Qed.

Theorem scheduler_state_preserves_memory :
  forall_endstates xTaskGetSchedulerState_armv6m_prog
    (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  unfold prog_noassign, xTaskGetSchedulerState_armv6m_prog.
  intros s a.
  destruct (existsb (N.eqb a) xTaskGetSchedulerState_armv6m_entries) eqn:IN;
    [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  cbn [xTaskGetSchedulerState_armv6m_entries] in IN.
  repeat destruct IN as [<-|IN]; try contradiction; prove_noassign.
Qed.

(* NEG then ADC cancels the value modulo 2^32 and retains the zero carry. *)
Lemma scheduler_state_adc_result : forall u,
  N.shiftl (((u + msub 32 0 u) mod 2^32 + N.b2n (u <=? 0)) mod 2^32) 1
    mod 2^32 = if u =? 0 then 2 else 0.
Proof.
  intro u. rewrite add_msub, mp2_mod_0_l, N.add_0_l.
  destruct u; reflexivity.
Qed.

Lemma scheduler_state_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.

Definition scheduler_state_entry_witness (m:memory) (lr:N) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ => N.ones (2^32)
  | R_LR => lr
  | _ => 0
  end.

Definition scheduler_state_readable (s:store) : Prop :=
  forall a, (0x20000024 <= a < 0x20000028 \/ 0x20000008 <= a < 0x2000000c) ->
    mem_readable s a.

Lemma scheduler_state_witness_models : forall m lr,
  m < 2^(8*2^32) -> lr < 2^32 ->
  models armv6mtypctx (scheduler_state_entry_witness m lr).
Proof.
  intros m lr B L v w T. destruct v; cbn [armv6mtypctx] in T;
    try discriminate; injection T as <-.
  all: lazymatch goal with
  | |- scheduler_state_entry_witness _ _ V_MEM32 < _ => exact B
  | |- scheduler_state_entry_witness _ _ A_READ < _ => exact (ones_bound (2^32))
  | |- scheduler_state_entry_witness _ _ R_LR < _ => exact L
  | |- _ < 2^?width => exact (scheduler_state_zero_bound width)
  end.
Qed.

Theorem scheduler_state_entry_satisfiable : forall m lr,
  m < 2^(8*2^32) -> N.odd lr = true -> lr < 0xfffffff0 ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\
    scheduler_state_readable s /\ s R_LR = lr /\
    N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.
Proof.
  intros m lr B O L. exists (scheduler_state_entry_witness m lr).
  split.
  - apply scheduler_state_witness_models; [exact B|]. change (lr < 2^32).
    eapply N.lt_trans; [exact L|reflexivity].
  - split; [reflexivity|]. split.
    + intros a RANGE. unfold mem_readable.
      change (N.testbit (N.ones (2^32)) a = true).
      apply N.ones_spec_low. clear - RANGE. destruct RANGE as [[LO HI]|[LO HI]];
        (eapply N.lt_trans; [exact HI|reflexivity]).
    + split; [reflexivity|]. split; assumption.
Qed.

Theorem scheduler_state_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x12fc,s))
  (MDL: models armv6mtypctx s),
  satisfies_all xTaskGetSchedulerState_armv6m_prog
    (scheduler_state_invariants s) scheduler_state_exit ((x',s')::t).
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.

Corollary scheduler_state_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x1310,s') = (Addr 0x12fc,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetSchedulerState_armv6m_prog ((Addr 0x1310,s')::t))
  (UT: unterminated scheduler_state_exit t),
  scheduler_state_postcondition s s'.
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.

Corollary scheduler_state_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x1310,s') = (Addr 0x12fc,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetSchedulerState_armv6m_prog ((Addr 0x1310,s')::t))
  (UT: unterminated scheduler_state_exit t),
  forall v, In v [R_R4; R_R5; R_R6; R_R7; R_R8; R_R9; R_R10; R_R11; R_SP; R_LR] ->
    s' v = s v.
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.

Corollary scheduler_state_original_memory : forall s t s'
  (ENTRY: startof t (Addr 0x1310,s') = (Addr 0x12fc,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetSchedulerState_armv6m_prog ((Addr 0x1310,s')::t))
  (UT: unterminated scheduler_state_exit t),
  s' V_MEM32 = s V_MEM32 /\
  forall a, (s' V_MEM32) Ⓑ[a] = (s V_MEM32) Ⓑ[a].
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.

Theorem scheduler_state_return_step : forall s
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  can_step xTaskGetSchedulerState_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x1310,s)).
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.

Corollary scheduler_state_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x1310,s') = (Addr 0x12fc,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetSchedulerState_armv6m_prog ((Addr 0x1310,s')::t))
  (UT: unterminated scheduler_state_exit t)
  (ODD: N.odd (s R_LR) = true) (ORDINARY: s R_LR < 0xfffffff0),
  scheduler_state_postcondition s s' /\
  can_step xTaskGetSchedulerState_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0x1310,s')).
Proof.
  (* Unfinished attempt preserved in notes/r19-scheduler-state-fix. *)
Abort.
