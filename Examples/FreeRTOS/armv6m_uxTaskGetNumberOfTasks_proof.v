(* uxTaskGetNumberOfTasks -- ARMv6-M Cortex-M0, sequential IL correctness.

   Initial author: OpenAI gpt-6-astra, xhigh (r06-task-count).
   One-shot initial proof; validation status is recorded in notes/r06-task-count.
   PROVENANCE: official FreeRTOS Kernel V11.1.0,
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Generated source: uxTaskGetNumberOfTasks_armv6m.v, armv6m_lifter.sh.
   Reviewed artifact prerequisite: e05 checkpoint 95da7ab7cee78f09a528aed86c1dfaf29520a9a8.

   ABI/spec: no register arguments. At entry 0x59c the folded immutable-code
   literal at 0x5a4 supplies 0x20000030 to R3. The load at 0x59e reads the
   four-byte little-endian uxCurrentNumberOfTasks word. At BX LR (0x5a0),
   R0 equals that word in INITIAL memory; all variables except R0/R3 agree
   with entry, including memory, SP, LR, R4-R11, and flags. The precondition
   is a modeled 32-bit ARMv6-M store. Actual executable traces provide the
   read-permission premises; a typed readable entry witness is supplied.
   There is no count/nonzero/path/size/overlap/CPU-feature/tunable bound.

   The invariant theorem is partial correctness up to the first BX LR.
   A separate modeled return step requires odd LR and clears its low bit.
   This is the ordinary branch behavior in this IL, NOT exception-return
   machinery or a theorem about hardware EXC_RETURN tokens. The finite
   generated _prog is used throughout; its default zero halfwords are not
   executable and the literal pool is not read from mutable data memory.
   No scheduler-cardinality invariant, IRQ/concurrency/atomicity model,
   termination theorem, or proved binary/lifter refinement is claimed.
 *)

Require Import Picinae_armv6m.
Require Import uxTaskGetNumberOfTasks_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition task_count_result (m:memory) : N := m Ⓓ[0x20000030].

Definition task_count_frame (initial final:store) : Prop :=
  forall v, v <> R_R0 -> v <> R_R3 -> final v = initial v.

Definition task_count_postcondition (initial final:store) : Prop :=
  final R_R0 = task_count_result (initial V_MEM32) /\
  task_count_frame initial final.

Definition task_count_exit (t:trace) : bool :=
  match t with (Addr 0x5a0,_)::_ => true | _ => false end.

Definition task_count_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x59c,s)::_ => Some (s = initial)
  | (Addr 0x5a0,s)::_ => Some (task_count_postcondition initial s)
  | _ => None
  end.

Theorem task_count_nwc : forall s2 s1,
  uxTaskGetNumberOfTasks_armv6m_prog s1 = uxTaskGetNumberOfTasks_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem task_count_welltyped :
  welltyped_prog armv6mtypctx uxTaskGetNumberOfTasks_armv6m_prog.
Proof. exact uxTaskGetNumberOfTasks_armv6m_welltyped. Qed.

Theorem task_count_preserves_memory :
  forall_endstates uxTaskGetNumberOfTasks_armv6m_prog
    (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  unfold prog_noassign, uxTaskGetNumberOfTasks_armv6m_prog.
  intros s a.
  destruct (existsb (N.eqb a) uxTaskGetNumberOfTasks_armv6m_entries) eqn:IN;
    [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  cbn [uxTaskGetNumberOfTasks_armv6m_entries] in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]]; prove_noassign.
Qed.

(* The bound lemma stays polymorphic in the width: do not evaluate 2^(8*2^32). *)
Lemma task_count_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.

Definition task_count_entry_witness (m:memory) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ => N.ones (2^32)
  | R_LR => 1
  | _ => 0
  end.

Definition task_count_readable (s:store) : Prop :=
  forall n, n < 4 -> mem_readable s ((0x20000030+n) mod 2^32).

Lemma task_count_witness_models : forall m,
  m < 2^(8*2^32) -> models armv6mtypctx (task_count_entry_witness m).
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Theorem task_count_entry_satisfiable : forall m,
  m < 2^(8*2^32) ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\
    task_count_readable s /\ N.odd (s R_LR) = true.
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Theorem task_count_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x59c,s))
  (MDL: models armv6mtypctx s),
  satisfies_all uxTaskGetNumberOfTasks_armv6m_prog
    (task_count_invariants s) task_count_exit ((x',s')::t).
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Corollary task_count_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x5a0,s') = (Addr 0x59c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskGetNumberOfTasks_armv6m_prog ((Addr 0x5a0,s')::t))
  (UT: unterminated task_count_exit t),
  task_count_postcondition s s'.
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Corollary task_count_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x5a0,s') = (Addr 0x59c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskGetNumberOfTasks_armv6m_prog ((Addr 0x5a0,s')::t))
  (UT: unterminated task_count_exit t),
  forall v, In v [R_R4; R_R5; R_R6; R_R7; R_R8; R_R9; R_R10; R_R11; R_SP; R_LR] ->
    s' v = s v.
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Theorem task_count_return_step : forall s (ODD: N.odd (s R_LR) = true),
  can_step uxTaskGetNumberOfTasks_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x5a0,s)).
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.

Corollary task_count_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x5a0,s') = (Addr 0x59c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog uxTaskGetNumberOfTasks_armv6m_prog ((Addr 0x5a0,s')::t))
  (UT: unterminated task_count_exit t)
  (ODD: N.odd (s R_LR) = true),
  task_count_postcondition s s' /\
  can_step uxTaskGetNumberOfTasks_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0x5a0,s')).
Proof.
  (* PARTIAL: initial attempt and diagnostics are preserved in notes/r06-task-count. *)
Abort.
