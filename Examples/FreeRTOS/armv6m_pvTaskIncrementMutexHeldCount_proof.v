(* pvTaskIncrementMutexHeldCount -- ARMv6-M sequential IL contract.
   Initial author: OpenAI gpt-6-astra, xhigh, service tier default; r18-mutex-held.
   Status: PARTIAL; first full build failed. Final proof producer: none.

   Provenance: official FreeRTOS V11.1.0 commit
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0; tasks.c SHA256
   6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149.
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Unchanged generated pvTaskIncrementMutexHeldCount_armv6m.v, armv6m_lifter.sh;
   accepted e05 call-free artifact via prerequisite 5fec2fc24d0c739bafc08add426f02a3085e15cd.
   Evidence: Examples/freertos/cortex-m0/evidence/{manifest,layout}.json,
   FreeRTOSConfig.h (configUSE_MUTEXES=1, 32-bit UBaseType_t/pointers),
   Examples/FreeRTOS/{abi,pvTaskIncrementMutexHeldCount}.json;
   notes/r18-mutex-held/05-provenance.log verifies selected hashes.
   TCB size 84, alignment 4, uxMutexesHeld offset 72; pxCurrentTCB=0x20000108.

   ABI/English specification: no register arguments. At entry 0x153c load
   p from the original four-byte little-endian pxCurrentTCB word. Return p
   in R0. If p=0, leave all memory unchanged. Otherwise load original count
   at (p+72) mod 2^32, increment modulo 2^32, and write exactly four bytes
   there. Preserve all variables except R0,R3,N,Z,C,V and the stated memory
   write; in particular R4-R11, SP, LR and permission maps are preserved.
   Literal at 0x154c is folded immutable code, not mutable data memory.

   Entry/BX cuts: 0x153c/0x154a; both NULL and non-NULL paths are included.
   The partial-correctness theorem requires a typed input; actual exec_prog
   traces supply load/store permission premises. Arbitrary typed-memory
   entry witnesses supply all read/write permissions and ordinary LR=1.
   No size/count/overflow/nonoverlap/alignment/CPU-feature/tunable restriction
   is needed for this IL contract: addresses wrap modulo 2^32, even if the
   write aliases the global pointer. Byte effects refer to ORIGINAL memory.
   A valid C object interpretation uses the pinned TCB layout; the theorem
   does not assert that an arbitrary nonzero pointer designates such an object.
   Ordinary BX is actually executed under odd LR < 0xfffffff0; a trace
   extension theorem records the same postcondition after that step.
   No callee oracle, IRQ/hardware/whole-kernel/cardinality/termination claim,
   no total execution-existence claim, and no proved binary/lifter refinement.
 *)
Require Import Picinae_armv6m.
Require Import pvTaskIncrementMutexHeldCount_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition mutex_held_current (m:memory) : N := m Ⓓ[0x20000108].
Definition mutex_held_address (m:memory) : N :=
  (mutex_held_current m + 72) mod 2^32.
Definition mutex_held_increment (m:memory) : N :=
  (m Ⓓ[mutex_held_address m] + 1) mod 2^32.
Definition mutex_held_memory (m:memory) : memory :=
  if mutex_held_current m =? 0 then m
  else m [Ⓓ mutex_held_address m := mutex_held_increment m].
Definition mutex_held_keep (v:var) : Prop :=
  match v with
  | V_MEM32 | R_R0 | R_R3 | F_N | F_Z | F_C | F_V => False
  | _ => True
  end.
Definition mutex_held_frame (initial final:store) : Prop :=
  forall v, mutex_held_keep v -> final v = initial v.
Definition mutex_held_postcondition (initial final:store) : Prop :=
  final R_R0 = mutex_held_current (initial V_MEM32) /\
  final V_MEM32 = mutex_held_memory (initial V_MEM32) /\
  mutex_held_frame initial final.
Definition mutex_held_exit (t:trace) : bool :=
  match t with (Addr 0x154a,_)::_ => true | _ => false end.
Definition mutex_held_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x153c,s)::_ => Some (s = initial)
  | (Addr 0x154a,s)::_ => Some (mutex_held_postcondition initial s)
  | _ => None
  end.
Definition mutex_held_ordinary_lr (lr:N) : Prop :=
  N.odd lr = true /\ lr < 0xfffffff0.
Definition mutex_held_permissions (s:store) : Prop :=
  (forall n, n < 4 -> mem_readable s ((0x20000108+n) mod 2^32)) /\
  (mutex_held_current (s V_MEM32) <> 0 -> forall n, n < 4 ->
    mem_readable s ((mutex_held_address (s V_MEM32)+n) mod 2^32) /\
    mem_writable s ((mutex_held_address (s V_MEM32)+n) mod 2^32)).

Theorem mutex_held_nwc : forall s2 s1,
  pvTaskIncrementMutexHeldCount_armv6m_prog s1 =
  pvTaskIncrementMutexHeldCount_armv6m_prog s2.
Proof. reflexivity. Qed.
Theorem mutex_held_welltyped :
  welltyped_prog armv6mtypctx pvTaskIncrementMutexHeldCount_armv6m_prog.
Proof. exact pvTaskIncrementMutexHeldCount_armv6m_welltyped. Qed.

Theorem mutex_held_register_frame : forall v, mutex_held_keep v ->
  forall_endstates pvTaskIncrementMutexHeldCount_armv6m_prog
    (fun _ s _ s' => s v = s' v).
Proof.
  intros v KEEP. apply noassign_prog_same.
  unfold prog_noassign, pvTaskIncrementMutexHeldCount_armv6m_prog. intros s a.
  destruct (existsb (N.eqb a) pvTaskIncrementMutexHeldCount_armv6m_entries) eqn:IN;
    [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  cbn [pvTaskIncrementMutexHeldCount_armv6m_entries] in IN.
  destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    destruct v; cbn [mutex_held_keep] in KEEP; try contradiction; prove_noassign.
Qed.

(* These algebraic facts state the original-memory effects, including wrap. *)
Theorem mutex_held_null_memory : forall m,
  mutex_held_current m = 0 -> mutex_held_memory m = m.
Proof. intros m NULL. unfold mutex_held_memory. rewrite NULL. reflexivity. Qed.
Theorem mutex_held_count_increment : forall m,
  mutex_held_current m <> 0 ->
  (mutex_held_memory m) Ⓓ[mutex_held_address m] = mutex_held_increment m.
Proof.
  intros m NONNULL. unfold mutex_held_memory.
  rewrite (proj2 (N.eqb_neq _ _) NONNULL).
  rewrite getmem_setmem by discriminate.
  unfold mutex_held_increment. apply N.mod_mod. discriminate.
Qed.
Theorem mutex_held_memory_frame : forall m a,
  (mutex_held_current m = 0 \/ 4 <= msub 32 a (mutex_held_address m)) ->
  (mutex_held_memory m) Ⓑ[a] = m Ⓑ[a].
Proof.
  intros m a [NULL|OUT].
  - rewrite (mutex_held_null_memory m NULL). reflexivity.
  - unfold mutex_held_memory. destruct (mutex_held_current m =? 0).
    + reflexivity.
    + rewrite !getmem_1. apply setmem_frame. exact OUT.
Qed.
Theorem mutex_held_written_bytes : forall m i,
  mutex_held_current m <> 0 -> i < 4 ->
  (mutex_held_memory m) Ⓑ[mutex_held_address m+i] =
  N.shiftr (mutex_held_increment m) (i*8) mod 256.
Proof.
  intros m i NONNULL LT. unfold mutex_held_memory.
  rewrite (proj2 (N.eqb_neq _ _) NONNULL), getmem_1.
  apply setmem_byte; [exact LT|discriminate].
Qed.

Lemma mutex_held_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.
Definition mutex_held_entry_store (m:memory) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ | A_WRITE => N.ones (2^32)
  | R_LR => 1
  | _ => 0
  end.
Theorem mutex_held_entry_models : forall m,
  m < 2^(8*2^32) -> models armv6mtypctx (mutex_held_entry_store m).
Proof.
  intros m B v w T. destruct v; cbn [armv6mtypctx] in T;
    try discriminate; injection T as <-.
  all: lazymatch goal with
  | |- mutex_held_entry_store _ V_MEM32 < _ => exact B
  | |- mutex_held_entry_store _ A_READ < _ => exact (ones_bound (2^32))
  | |- mutex_held_entry_store _ A_WRITE < _ => exact (ones_bound (2^32))
  | |- mutex_held_entry_store _ R_LR < _ => change (1 < 2^32); reflexivity
  | |- _ < 2^?width => exact (mutex_held_zero_bound width)
  end.
Qed.
Theorem mutex_held_entry_satisfiable : forall m,
  m < 2^(8*2^32) -> exists s,
    models armv6mtypctx s /\ s V_MEM32 = m /\
    mutex_held_permissions s /\ mutex_held_ordinary_lr (s R_LR).
Proof.
  intros m B. exists (mutex_held_entry_store m).
  split; [apply mutex_held_entry_models; exact B|].
  split; [reflexivity|]. split.
  - unfold mutex_held_permissions. split.
    + intros n LT. unfold mem_readable.
      change (N.testbit (N.ones (2^32)) ((0x20000108+n) mod 2^32) = true).
      apply N.ones_spec_low. apply N.mod_lt, pow2_nonzero.
    + intros NONNULL n LT. split; unfold mem_readable, mem_writable;
        change (N.testbit (N.ones (2^32))
          ((mutex_held_address m+n) mod 2^32) = true);
        apply N.ones_spec_low; apply N.mod_lt, pow2_nonzero.
  - split; reflexivity.
Qed.

(* In particular every 32-bit current pointer, including NULL, is realizable. *)
Theorem mutex_held_current_satisfiable : forall p, p < 2^32 -> exists s,
  models armv6mtypctx s /\ mutex_held_permissions s /\
  mutex_held_ordinary_lr (s R_LR) /\ mutex_held_current (s V_MEM32) = p.
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.

Theorem mutex_held_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x153c,s))
  (MDL: models armv6mtypctx s),
  satisfies_all pvTaskIncrementMutexHeldCount_armv6m_prog
    (mutex_held_invariants s) mutex_held_exit ((x',s')::t).
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.

Corollary mutex_held_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x154a,s') = (Addr 0x153c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog pvTaskIncrementMutexHeldCount_armv6m_prog ((Addr 0x154a,s')::t))
  (UT: unterminated mutex_held_exit t),
  mutex_held_postcondition s s'.
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.
Corollary mutex_held_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x154a,s') = (Addr 0x153c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog pvTaskIncrementMutexHeldCount_armv6m_prog ((Addr 0x154a,s')::t))
  (UT: unterminated mutex_held_exit t),
  forall v, In v [R_R4;R_R5;R_R6;R_R7;R_R8;R_R9;R_R10;R_R11;R_SP;R_LR] ->
    s' v = s v.
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.

Theorem mutex_held_return_step : forall s,
  mutex_held_ordinary_lr (s R_LR) ->
  can_step pvTaskIncrementMutexHeldCount_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x154a,s)).
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.
Corollary mutex_held_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x154a,s') = (Addr 0x153c,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog pvTaskIncrementMutexHeldCount_armv6m_prog ((Addr 0x154a,s')::t))
  (UT: unterminated mutex_held_exit t)
  (LR: mutex_held_ordinary_lr (s R_LR)),
  mutex_held_postcondition s s' /\
  exec_prog pvTaskIncrementMutexHeldCount_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s')::(Addr 0x154a,s')::t).
Proof.
  (* PARTIAL: exact initial attempt and first-build diagnostics are in
     notes/r18-mutex-held; Astra one-shot policy requires a Sol handoff. *)
Abort.
