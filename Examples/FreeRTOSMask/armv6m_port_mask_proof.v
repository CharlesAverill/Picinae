(* FreeRTOS V11.1.0 Cortex-M0 port mask callees.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, r42-port-mask.
   Source dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   ELF .toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf
   SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Inherited e19 strict primask-v1-base finite lifts, unchanged here.

   ABI/spec: 32-bit ARMv6-M registers and pointers, CONTROL.nPRIV=0;
   either typed Thread or Handler mode. LR is odd and below 0xfffffff0.
   Set (0x4090 MRS; 0x4094 CPSID; 0x4096 BX LR) returns the old typed
   one-bit PRIMASK in R0 and sets PRIMASK=1. Clear (0x4098 MSR; 0x409c
   BX LR) writes R0 mod 2 to PRIMASK and preserves R0. Both preserve all
   memory, SP, LR, R1-R12, NZCV, access maps, temporaries, mode and CONTROL.
   No buffer sizes, overlap restrictions, memory permissions or tunables:
   neither body accesses memory. Arbitrary typed memory is supported.

   Statements concern sequential executions of these actual finite IL maps.
   Code stability needs unchanged CONTROL.nPRIV and LR, not a false global
   store-independent nwc assertion. The BX is an actual modeled step, not
   merely an exit predicate. EXC_RETURN is excluded. No asynchronous IRQ
   exclusion/delivery, barrier, scheduler, termination or binary/lifter
   refinement claim. The finite execution witness is not a total-correctness
   theorem about the caller's continuation or the physical machine. *)
From Stdlib Require Import NArith List Bool Lia FunctionalExtensionality.
Require Import Picinae_armv6m.
Require Import Picinae.Examples.FreeRTOSMask.ulSetInterruptMask_armv6m.
Require Import Picinae.Examples.FreeRTOSMask.vClearInterruptMask_armv6m.
Import ListNotations.
Open Scope N.

Definition mask_entry (s:store) : Prop :=
  models armv6mtypctx s /\ s S_CONTROL_NPRIV = 0 /\
  N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.
Definition mask_return (s:store) := N.land (s R_LR) 0xfffffffe.
Definition mask_set_mrs (s:store) := update s R_R0 (s S_PRIMASK).
Definition mask_set_result (s:store) := update (mask_set_mrs s) S_PRIMASK 1.
Definition mask_clear_result (s:store) := update s S_PRIMASK (s R_R0 mod 2).
Definition mask_set_frame (s s':store) :=
  forall v, v <> R_R0 -> v <> S_PRIMASK -> s' v = s v.
Definition mask_clear_frame (s s':store) :=
  forall v, v <> S_PRIMASK -> s' v = s v.
Definition mask_set_postcondition (s s':store) :=
  s' R_R0 = s S_PRIMASK /\ s' S_PRIMASK = 1 /\
  s' R_R0 < 2 /\ mask_set_frame s s'.
Definition mask_clear_postcondition (s s':store) :=
  s' S_PRIMASK = s R_R0 mod 2 /\ mask_clear_frame s s'.
Definition mask_set_exit (t:trace) :=
  match t with (Addr 0x4096,_)::_ => true | _ => false end.
Definition mask_clear_exit (t:trace) :=
  match t with (Addr 0x409c,_)::_ => true | _ => false end.
Definition mask_set_invs (s0:store) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x4090 => Some (s = s0 /\ mask_entry s0)
  | 0x4096 => Some (s = mask_set_result s0 /\ mask_set_postcondition s0 s)
  | _ => None end | _ => None end.
Definition mask_clear_invs (s0:store) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x4098 => Some (s = s0 /\ mask_entry s0)
  | 0x409c => Some (s = mask_clear_result s0 /\ mask_clear_postcondition s0 s)
  | _ => None end | _ => None end.

Theorem port_set_welltyped : welltyped_prog armv6mtypctx ulSetInterruptMask_prog.
Proof. exact ulSetInterruptMask_welltyped. Qed.
Theorem port_clear_welltyped : welltyped_prog armv6mtypctx vClearInterruptMask_prog.
Proof. exact vClearInterruptMask_welltyped. Qed.

Theorem mask_set_result_frame : forall s, mask_set_frame s (mask_set_result s).
Proof. intros s v H0 HP. unfold mask_set_result, mask_set_mrs.
  rewrite !update_frame by assumption. reflexivity. Qed.
Theorem mask_clear_result_frame : forall s, mask_clear_frame s (mask_clear_result s).
Proof. intros s v HP. unfold mask_clear_result. apply update_frame, HP. Qed.
Theorem mask_set_result_post : forall s, models armv6mtypctx s ->
  mask_set_postcondition s (mask_set_result s).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem mask_clear_result_post : forall s,
  mask_clear_postcondition s (mask_clear_result s).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

(* A typed starting store exists for every supported memory/argument/SP. *)
Definition mask_input_store m arg sp : store :=
  update (update (update (fun _ => 0) V_MEM32 m) R_R0 arg) R_SP sp.
Theorem mask_input_store_typed : forall m arg sp,
  m < 2^(8*2^32) -> arg < 2^32 -> sp < 2^32 ->
  models armv6mtypctx (mask_input_store m arg sp).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

(* Inhabitance for every typed input store, either mask bit and either mode.
   In particular memory, SP, R0 and access maps are unrestricted typed inputs. *)
Definition mask_entry_store (s:store) p h lr :=
  update (update (update (update s S_PRIMASK p) S_HANDLER h)
    S_CONTROL_NPRIV 0) R_LR lr.
Theorem mask_entry_witness : forall s p h lr,
  models armv6mtypctx s -> p < 2 -> h < 2 ->
  N.odd lr = true -> lr < 0xfffffff0 ->
  mask_entry (mask_entry_store s p h lr) /\
  mask_entry_store s p h lr S_PRIMASK = p /\
  mask_entry_store s p h lr V_MEM32 = s V_MEM32 /\
  mask_entry_store s p h lr R_R0 = s R_R0 /\
  mask_entry_store s p h lr R_SP = s R_SP.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem mask_both_bits_inhabited : forall s h lr,
  models armv6mtypctx s -> h < 2 -> N.odd lr = true -> lr < 0xfffffff0 ->
  mask_entry (mask_entry_store s 0 h lr) /\
  mask_entry (mask_entry_store s 1 h lr).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

Lemma mask_reset_same : forall s, reset_temps s s = s.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_reset_update : forall s v n w, armv6mtypctx v = Some w ->
  reset_temps s (update s v n) = update s v n.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

Definition mask_mrs_stmt := Move R_R0 armv6m_read_primask.
Definition mask_cps_stmt := armv6m_write_primask (Word 1 1).
Definition mask_msr_stmt := armv6m_write_primask (Cast CAST_LOW 1 (Var R_R0)).
Definition mask_bx_stmt := armv6m_bxwritepc (Var R_LR).

Lemma mask_set_lookup_mrs : forall s, s S_CONTROL_NPRIV = 0 ->
  ulSetInterruptMask_prog s 0x4090 = Some (4,mask_mrs_stmt).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_set_lookup_cps : forall s, s S_CONTROL_NPRIV = 0 ->
  ulSetInterruptMask_prog s 0x4094 = Some (2,mask_cps_stmt).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_clear_lookup_msr : forall s, s S_CONTROL_NPRIV = 0 ->
  vClearInterruptMask_prog s 0x4098 = Some (4,mask_msr_stmt).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_set_lookup_bx : forall s, s S_CONTROL_NPRIV = 0 ->
  s R_LR < 0xfffffff0 -> ulSetInterruptMask_prog s 0x4096 = Some (2,mask_bx_stmt).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_clear_lookup_bx : forall s, s S_CONTROL_NPRIV = 0 ->
  s R_LR < 0xfffffff0 -> vClearInterruptMask_prog s 0x409c = Some (2,mask_bx_stmt).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

(* Conditional nwc, including stores outside the supported profile. *)
Theorem mask_set_code_stable : forall s t,
  s S_CONTROL_NPRIV = t S_CONTROL_NPRIV -> s R_LR = t R_LR ->
  forall a, ulSetInterruptMask_prog s a = ulSetInterruptMask_prog t a.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem mask_clear_code_stable : forall s t,
  s S_CONTROL_NPRIV = t S_CONTROL_NPRIV -> s R_LR = t R_LR ->
  forall a, vClearInterruptMask_prog s a = vClearInterruptMask_prog t a.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

Lemma mask_privileged_eval : forall s, models armv6mtypctx s ->
  s S_CONTROL_NPRIV = 0 -> eval_exp armv6mtypctx s armv6m_privileged 1 1.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_mrs_exec : forall s, models armv6mtypctx s -> s S_CONTROL_NPRIV = 0 ->
  exec_stmt armv6mtypctx s mask_mrs_stmt (update armv6mtypctx R_R0 (Some 32))
    (mask_set_mrs s) None.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_write_exec : forall s e n, models armv6mtypctx s ->
  s S_CONTROL_NPRIV = 0 -> eval_exp armv6mtypctx s e n 1 ->
  exec_stmt armv6mtypctx s (armv6m_write_primask e)
    (update armv6mtypctx S_PRIMASK (Some 1)) (update s S_PRIMASK n) None.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_bx_exec : forall s, N.odd (s R_LR) = true ->
  exec_stmt armv6mtypctx s mask_bx_stmt armv6mtypctx s (Some (Addr (mask_return s))).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

Lemma mask_move_step : forall p a sz s v n w e,
  p s a = Some (sz,Move v e) -> armv6mtypctx v = Some w ->
  eval_exp armv6mtypctx s e n w ->
  can_step p ((Addr (a+sz),update s v n),(Addr a,s)).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_return_step : forall p a s,
  p s a = Some (2,mask_bx_stmt) -> N.odd (s R_LR) = true ->
  can_step p ((Addr (mask_return s),s),(Addr a,s)).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Lemma mask_step_unique : forall p a s sz q c' s' x,
  p s a = Some (sz,q) -> forall_exps_in_stmt not_unknown q ->
  exec_stmt armv6mtypctx s q c' s' x -> forall z,
  can_step p (z,(Addr a,s)) -> z = (exitof (a+sz) x,reset_temps s s').
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

Theorem mask_set_execution : forall s, mask_entry s ->
  can_step ulSetInterruptMask_prog ((Addr 0x4094,mask_set_mrs s),(Addr 0x4090,s)) /\
  can_step ulSetInterruptMask_prog ((Addr 0x4096,mask_set_result s),(Addr 0x4094,mask_set_mrs s)) /\
  can_step ulSetInterruptMask_prog ((Addr (mask_return s),mask_set_result s),(Addr 0x4096,mask_set_result s)) /\
  mask_set_postcondition s (mask_set_result s).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem mask_clear_execution : forall s, mask_entry s ->
  can_step vClearInterruptMask_prog ((Addr 0x409c,mask_clear_result s),(Addr 0x4098,s)) /\
  can_step vClearInterruptMask_prog ((Addr (mask_return s),mask_clear_result s),(Addr 0x409c,mask_clear_result s)) /\
  mask_clear_postcondition s (mask_clear_result s).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

(* Universal completed-step specifications, paired above with concrete paths.
   No desired result, callee contract, or assumed execution oracle is a premise. *)
Theorem ulSetInterruptMask_correct : forall s s1 s2 s3 x1 x2 x3,
  mask_entry s ->
  can_step ulSetInterruptMask_prog ((x1,s1),(Addr 0x4090,s)) ->
  can_step ulSetInterruptMask_prog ((x2,s2),(x1,s1)) ->
  can_step ulSetInterruptMask_prog ((x3,s3),(x2,s2)) ->
  x3 = Addr (mask_return s) /\ s3 = mask_set_result s /\ mask_set_postcondition s s3.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem vClearInterruptMask_correct : forall s s1 s2 x1 x2,
  mask_entry s ->
  can_step vClearInterruptMask_prog ((x1,s1),(Addr 0x4098,s)) ->
  can_step vClearInterruptMask_prog ((x2,s2),(x1,s1)) ->
  x2 = Addr (mask_return s) /\ s2 = mask_clear_result s /\ mask_clear_postcondition s s2.
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.

(* Floyd-Hoare interface to the return-instruction cut. The separate execution
   and completed-step theorems above include BX, including its dynamic guard. *)
Theorem ulSetInterruptMask_satisfies_all : forall s t s' x',
  startof t (x',s') = (Addr 0x4090,s) -> mask_entry s ->
  satisfies_all ulSetInterruptMask_prog (mask_set_invs s) mask_set_exit ((x',s')::t).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
Theorem vClearInterruptMask_satisfies_all : forall s t s' x',
  startof t (x',s') = (Addr 0x4098,s) -> mask_entry s ->
  satisfies_all vClearInterruptMask_prog (mask_clear_invs s) mask_clear_exit ((x',s')::t).
(* Unchecked one-shot proof preserved in notes/r42-port-mask/initial-attempt.v.txt. *)
Abort.
