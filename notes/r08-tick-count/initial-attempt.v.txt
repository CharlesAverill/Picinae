(* xTaskGetTickCount -- ARMv6-M Cortex-M0, sequential IL correctness.

   Initial author: OpenAI gpt-6-astra, xhigh, r08-tick-count.
   One-shot proof attempt; validation and final producer: notes/r08-tick-count.
   Adapted from the accepted r06 Astra/Sol getter proof at 5fec2fc24d0c739bafc08add426f02a3085e15cd.
   PROVENANCE: official FreeRTOS Kernel V11.1.0,
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0; tasks.c SHA256
   6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149.
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Generated xTaskGetTickCount_armv6m.v is unchanged; armv6m_lifter.sh.
   Evidence: xTaskGetTickCount.json, abi.json, and the pinned fixture's
   evidence/{manifest,layout,symbols}.json, nm.txt and FreeRTOSConfig.h.
   The 4-byte xTickCount object is at 0x2000002c, offset zero;
   TickType_t and pointers are 4 bytes, tick width 32, one core, trace off.
   ARM_CM0 portTICK_TYPE_IS_ATOMIC=1 removes the tick critical macros in
   this build. That source fact explains the call-free body; this proof
   establishes no hardware atomicity or IRQ property.

   ABI/spec: no register arguments. Entry 0x584 folds immutable pool bytes
   at 0x58c into R3=0x2000002c. LDR at 0x586 reads four little-endian bytes.
   At the first BX LR cut 0x588, R0 is the INITIAL memory word there;
   all variables other than R0/R3 equal entry, including all memory bytes,
   permissions, SP, LR, R4-R11 and flags. No memory writes or callees.
   The input is any modeled 32-bit ARMv6-M store; executable traces carry
   the read-permission premises. The entry witness accepts every bounded
   memory, grants read permission, and has an ordinary valid LR=1.
   There are no value/nonzero/size/overlap/CPU-feature/tunable restrictions.
   Caller/return-step theorems additionally require odd LR < 0xfffffff0,
   explicitly excluding EXC_RETURN. The actual finite program's BX step
   clears LR bit zero and leaves the complete store unchanged.

   Invariant correctness is conditional on execution up to the first cut,
   not a termination theorem. The default zero halfwords and literal pool
   are not executable entries. Immutable pool folding, ISA/lifter and ELF
   provenance remain trusted; no binary refinement, exception machinery,
   IRQ/interleaving, whole-kernel or scheduler-cardinality claim is made.
 *)

Require Import Picinae_armv6m.
Require Import xTaskGetTickCount_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition tick_count_result (m:memory) : N := m Ⓓ[0x2000002c].

Definition tick_count_frame (initial final:store) : Prop :=
  forall v, v <> R_R0 -> v <> R_R3 -> final v = initial v.

Definition tick_count_postcondition (initial final:store) : Prop :=
  final R_R0 = tick_count_result (initial V_MEM32) /\
  tick_count_frame initial final.

Definition tick_count_exit (t:trace) : bool :=
  match t with (Addr 0x588,_)::_ => true | _ => false end.

Definition tick_count_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x584,s)::_ => Some (s = initial)
  | (Addr 0x588,s)::_ => Some (tick_count_postcondition initial s)
  | _ => None
  end.

Theorem tick_count_nwc : forall s2 s1,
  xTaskGetTickCount_armv6m_prog s1 = xTaskGetTickCount_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem tick_count_welltyped :
  welltyped_prog armv6mtypctx xTaskGetTickCount_armv6m_prog.
Proof. exact xTaskGetTickCount_armv6m_welltyped. Qed.

Theorem tick_count_preserves_memory :
  forall_endstates xTaskGetTickCount_armv6m_prog
    (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  unfold prog_noassign, xTaskGetTickCount_armv6m_prog.
  intros s a.
  destruct (existsb (N.eqb a) xTaskGetTickCount_armv6m_entries) eqn:IN;
    [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  cbn [xTaskGetTickCount_armv6m_entries] in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]]; prove_noassign.
Qed.

(* The bound lemma stays polymorphic in the width: do not evaluate 2^(8*2^32). *)
Lemma tick_count_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.

Definition tick_count_entry_witness (m:memory) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ => N.ones (2^32)
  | R_LR => 1
  | _ => 0
  end.

Definition tick_count_readable (s:store) : Prop :=
  forall n, n < 4 -> mem_readable s ((0x2000002c+n) mod 2^32).

Lemma tick_count_witness_models : forall m,
  m < 2^(8*2^32) -> models armv6mtypctx (tick_count_entry_witness m).
Proof.
  intros m B v w T. destruct v; cbn [armv6mtypctx] in T;
    try discriminate; injection T as <-.
  (* Select by constructor before conversion: in particular never try the
     memory bound against the enormous all-readable permission bitmap. *)
  all: lazymatch goal with
  | |- tick_count_entry_witness _ V_MEM32 < _ => exact B
  | |- tick_count_entry_witness _ A_READ < _ => exact (ones_bound (2^32))
  | |- tick_count_entry_witness _ R_LR < _ => change (1 < 2^32); reflexivity
  | |- _ < 2^?width => exact (tick_count_zero_bound width)
  end.
Qed.

Theorem tick_count_entry_satisfiable : forall m,
  m < 2^(8*2^32) ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\
    tick_count_readable s /\ N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.
Proof.
  intros m B. exists (tick_count_entry_witness m).
  split. apply tick_count_witness_models, B.
  split. reflexivity.
  split.
  - intros n LT. unfold mem_readable.
    change (N.testbit (N.ones (2^32)) ((0x2000002c+n) mod 2^32) = true).
    apply N.ones_spec_low. apply N.mod_lt, pow2_nonzero.
  - split; reflexivity.
Qed.

Theorem tick_count_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x584,s))
  (MDL: models armv6mtypctx s),
  satisfies_all xTaskGetTickCount_armv6m_prog
    (tick_count_invariants s) tick_count_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. armv6m_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply tick_count_welltyped. intro MDL1.
    clear - PRE MDL1. rename t1 into t.
    destruct_inv 32 PRE.
    subst s1.
    repeat armv6m_step.
    unfold tick_count_postcondition, tick_count_result, tick_count_frame.
    split. reflexivity.
    intros v NE0 NE3. destruct v; try contradiction; reflexivity.
Qed.

Corollary tick_count_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x588,s') = (Addr 0x584,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCount_armv6m_prog ((Addr 0x588,s')::t))
  (UT: unterminated tick_count_exit t),
  tick_count_postcondition s s'.
Proof.
  intros.
  pose proof (tick_count_correct s t s' (Addr 0x588) ENTRY MDL) as ALL.
  pose proof (satall_trueif_inv _ _ _ _ ALL EXEC UT) as POST.
  exact POST.
Qed.

Corollary tick_count_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x588,s') = (Addr 0x584,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCount_armv6m_prog ((Addr 0x588,s')::t))
  (UT: unterminated tick_count_exit t),
  forall v, In v [R_R4; R_R5; R_R6; R_R7; R_R8; R_R9; R_R10; R_R11; R_SP; R_LR] ->
    s' v = s v.
Proof.
  intros s t s' ENTRY MDL EXEC UT v IN.
  pose proof (proj2 (tick_count_post_at_bx s t s' ENTRY MDL EXEC UT)) as FRAME.
  apply FRAME; intro EQ; subst v; cbn in IN; intuition discriminate.
Qed.

Theorem tick_count_return_step : forall s
  (ODD: N.odd (s R_LR) = true)
  (ORDINARY: s R_LR < 0xfffffff0),
  can_step xTaskGetTickCount_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x588,s)).
Proof.
  intros s ODD ORDINARY.
  assert (LOW: s R_LR mod 2 = 1).
  { apply mod2_1_neven. rewrite <- N.negb_odd, ODD. reflexivity. }
  assert (XS: exec_stmt armv6mtypctx s (armv6m_bxwritepc (Var R_LR))
    armv6mtypctx s (Some (Addr (N.land (s R_LR) (N.ones 32 - 1))))).
  { unfold armv6m_bxwritepc. eapply XIf with (b:=1).
    - assert (E: eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR))
        (s R_LR mod 2) 1).
      { apply ECast with (w:=32) (n:=s R_LR). apply EVar. reflexivity. }
      rewrite LOW in E. exact E.
    - apply XJmp with (w:=32).
      apply EBinOp with (w:=32) (n1:=s R_LR) (n2:=N.ones 32 - 1);
        [apply EVar; reflexivity | apply EWord]. }
  assert (CS: can_step xTaskGetTickCount_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),reset_temps s s),(Addr 0x588,s))).
  { eapply CanStep with (sz:=2) (q:=armv6m_bxwritepc (Var R_LR))
      (x:=Some (Addr (N.land (s R_LR) (N.ones 32 - 1))));
      [reflexivity | exact XS]. }
  assert (RESET: reset_temps s s = s).
  { extensionality v. destruct v; reflexivity. }
  rewrite RESET in CS. exact CS.
Qed.

Corollary tick_count_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x588,s') = (Addr 0x584,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCount_armv6m_prog ((Addr 0x588,s')::t))
  (UT: unterminated tick_count_exit t)
  (ODD: N.odd (s R_LR) = true)
  (ORDINARY: s R_LR < 0xfffffff0),
  tick_count_postcondition s s' /\
  can_step xTaskGetTickCount_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0x588,s')).
Proof.
  intros.
  pose proof (tick_count_post_at_bx s t s' ENTRY MDL EXEC UT) as POST.
  assert (LR: s' R_LR = s R_LR) by (apply (proj2 POST); discriminate).
  split. exact POST.
  rewrite <- LR. apply tick_count_return_step; rewrite LR; assumption.
Qed.

(* Explicit original-memory byte effects: every address is preserved. *)
Corollary tick_count_preserves_original_bytes : forall s t s'
  (ENTRY: startof t (Addr 0x588,s') = (Addr 0x584,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCount_armv6m_prog ((Addr 0x588,s')::t))
  (UT: unterminated tick_count_exit t),
  s' V_MEM32 = s V_MEM32 /\
  forall a, (s' V_MEM32) Ⓑ[a] = (s V_MEM32) Ⓑ[a].
Proof.
  intros s t s' ENTRY MDL EXEC UT.
  pose proof (proj2 (tick_count_post_at_bx s t s' ENTRY MDL EXEC UT)) as FRAME.
  assert (MEM: s' V_MEM32 = s V_MEM32) by (apply FRAME; discriminate).
  split. exact MEM.
  intro a. rewrite MEM. reflexivity.
Qed.
