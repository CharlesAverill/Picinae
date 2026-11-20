(* xTaskGetTickCountFromISR -- ARMv6-M Cortex-M0 sequential IL correctness.

   Initial author: OpenAI gpt-6-astra, xhigh, r09-tick-count-isr.
   One-shot proof attempt; validation/model outcome: notes/r09-tick-count-isr.
   Adapted from accepted r06 (Astra statements, Sol completed proof), exact
   prerequisite 5fec2fc24d0c739bafc08add426f02a3085e15cd. No r06 theorem imported.

   PROVENANCE: official FreeRTOS Kernel V11.1.0 commit
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0; ELF
   /home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf
   SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Unchanged generated xTaskGetTickCountFromISR_armv6m.v, armv6m_lifter.sh.
   xTaskGetTickCountFromISR.json records the literal, instructions, zero calls
   and tasks.c SHA256 6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149.
   abi.json and ../freertos/cortex-m0/evidence/{layout.json,nm.txt} identify
   xTickCount at 0x2000002c, object offset 0, size 4, and TickType_t size 4.
   ../freertos/cortex-m0/FreeRTOSConfig.h pins 32-bit ticks and one core.

   English/ABI spec: no register arguments, 32-bit pointers and registers.
   Entry 0x590 folds the immutable code literal at 0x598 into R3; instruction
   0x592 reads the four-byte little-endian xTickCount word into R0. At the
   first BX LR cut 0x594, R0 equals that word in INITIAL memory. Every variable
   except R0/R3 is unchanged: all memory bytes, permissions, flags, R4-R11,
   SP, LR and temporaries. No stack access, callee, or callee oracle occurs.

   Precondition: a modeled ARMv6-M store. Actual execution premises supply
   read permissions; a typed/permitted witness is given for EVERY bounded
   architectural memory value. No nonzero, tick-count value, size, overlap,
   path-length, CPU-feature or tunable restriction is imposed. The return
   theorems additionally require odd LR below 0xfffffff0, excluding EXC_RETURN,
   and exhibit the actual generated BX step to LR with bit zero cleared,
   with exactly the same store. This guard scopes ordinary branch behavior;
   the inherited IL does not implement exception-return machinery.

   The finite generated _prog is used throughout. Padding at 0x596 is not
   reached before the designated exit; literals are not executable entries.
   This is sequential partial correctness, NOT asynchronous ISR atomicity,
   CPU interrupt/hardware correctness, whole-kernel invariants, cardinality,
   termination, or a proved binary/lifter refinement. Folded literals and
   inherited extraction provenance remain trusted. No lift repair is made.
 *)

Require Import Picinae_armv6m.
Require Import xTaskGetTickCountFromISR_armv6m.
From Stdlib Require Import NArith List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition tick_count_isr_result (m:memory) : N := m Ⓓ[0x2000002c].

Definition tick_count_isr_frame (initial final:store) : Prop :=
  forall v, v <> R_R0 -> v <> R_R3 -> final v = initial v.

Definition tick_count_isr_postcondition (initial final:store) : Prop :=
  final R_R0 = tick_count_isr_result (initial V_MEM32) /\
  tick_count_isr_frame initial final.

Definition tick_count_isr_exit (t:trace) : bool :=
  match t with (Addr 0x594,_)::_ => true | _ => false end.

Definition tick_count_isr_invariants (initial:store) (t:trace) : option Prop :=
  match t with
  | (Addr 0x590,s)::_ => Some (s = initial)
  | (Addr 0x594,s)::_ => Some (tick_count_isr_postcondition initial s)
  | _ => None
  end.

Theorem tick_count_isr_nwc : forall s2 s1,
  xTaskGetTickCountFromISR_armv6m_prog s1 = xTaskGetTickCountFromISR_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem tick_count_isr_welltyped :
  welltyped_prog armv6mtypctx xTaskGetTickCountFromISR_armv6m_prog.
Proof. exact xTaskGetTickCountFromISR_armv6m_welltyped. Qed.

Theorem tick_count_isr_preserves_memory :
  forall_endstates xTaskGetTickCountFromISR_armv6m_prog
    (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  unfold prog_noassign, xTaskGetTickCountFromISR_armv6m_prog.
  intros s a.
  destruct (existsb (N.eqb a) xTaskGetTickCountFromISR_armv6m_entries) eqn:IN;
    [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  cbn [xTaskGetTickCountFromISR_armv6m_entries] in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]]; prove_noassign.
Qed.

(* The bound lemma stays polymorphic in the width: do not evaluate 2^(8*2^32). *)
Lemma tick_count_isr_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.

Definition tick_count_isr_entry_witness (m:memory) : store := fun v =>
  match v with
  | V_MEM32 => m
  | A_READ => N.ones (2^32)
  | R_LR => 1
  | _ => 0
  end.

Definition tick_count_isr_readable (s:store) : Prop :=
  forall n, n < 4 -> mem_readable s ((0x2000002c+n) mod 2^32).

Lemma tick_count_isr_witness_models : forall m,
  m < 2^(8*2^32) -> models armv6mtypctx (tick_count_isr_entry_witness m).
Proof.
  intros m B v w T. destruct v; cbn [armv6mtypctx] in T;
    try discriminate; injection T as <-.
  (* Select by constructor before conversion: in particular never try the
     memory bound against the enormous all-readable permission bitmap. *)
  all: lazymatch goal with
  | |- tick_count_isr_entry_witness _ V_MEM32 < _ => exact B
  | |- tick_count_isr_entry_witness _ A_READ < _ => exact (ones_bound (2^32))
  | |- tick_count_isr_entry_witness _ R_LR < _ => change (1 < 2^32); reflexivity
  | |- _ < 2^?width => exact (tick_count_isr_zero_bound width)
  end.
Qed.

Theorem tick_count_isr_entry_satisfiable : forall m,
  m < 2^(8*2^32) ->
  exists s, models armv6mtypctx s /\ s V_MEM32 = m /\
    tick_count_isr_readable s /\ N.odd (s R_LR) = true /\
    s R_LR < 0xfffffff0.
Proof.
  intros m B. exists (tick_count_isr_entry_witness m).
  split. apply tick_count_isr_witness_models, B.
  split. reflexivity.
  split.
  - intros n LT. unfold mem_readable.
    change (N.testbit (N.ones (2^32)) ((0x2000002c+n) mod 2^32) = true).
    apply N.ones_spec_low. apply N.mod_lt, pow2_nonzero.
  - split; reflexivity.
Qed.

Theorem tick_count_isr_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x590,s))
  (MDL: models armv6mtypctx s),
  satisfies_all xTaskGetTickCountFromISR_armv6m_prog
    (tick_count_isr_invariants s) tick_count_isr_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. armv6m_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply tick_count_isr_welltyped. intro MDL1.
    clear - PRE MDL1. rename t1 into t.
    destruct_inv 32 PRE.
    subst s1.
    repeat armv6m_step.
    unfold tick_count_isr_postcondition, tick_count_isr_result, tick_count_isr_frame.
    split. reflexivity.
    intros v NE0 NE3. destruct v; try contradiction; reflexivity.
Qed.

Corollary tick_count_isr_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x594,s') = (Addr 0x590,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCountFromISR_armv6m_prog ((Addr 0x594,s')::t))
  (UT: unterminated tick_count_isr_exit t),
  tick_count_isr_postcondition s s'.
Proof.
  intros.
  pose proof (tick_count_isr_correct s t s' (Addr 0x594) ENTRY MDL) as ALL.
  pose proof (satall_trueif_inv _ _ _ _ ALL EXEC UT) as POST.
  exact POST.
Qed.

Corollary tick_count_isr_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x594,s') = (Addr 0x590,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCountFromISR_armv6m_prog ((Addr 0x594,s')::t))
  (UT: unterminated tick_count_isr_exit t),
  forall v, In v [R_R4; R_R5; R_R6; R_R7; R_R8; R_R9; R_R10; R_R11; R_SP; R_LR] ->
    s' v = s v.
Proof.
  intros s t s' ENTRY MDL EXEC UT v IN.
  pose proof (proj2 (tick_count_isr_post_at_bx s t s' ENTRY MDL EXEC UT)) as FRAME.
  apply FRAME; intro EQ; subst v; cbn in IN; intuition discriminate.
Qed.

Corollary tick_count_isr_original_bytes : forall s t s'
  (ENTRY: startof t (Addr 0x594,s') = (Addr 0x590,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCountFromISR_armv6m_prog ((Addr 0x594,s')::t))
  (UT: unterminated tick_count_isr_exit t),
  s' R_R0 = (s V_MEM32) Ⓓ[0x2000002c] /\
  forall a, (s' V_MEM32) Ⓑ[a] = (s V_MEM32) Ⓑ[a].
Proof.
  intros s t s' ENTRY MDL EXEC UT.
  pose proof (tick_count_isr_post_at_bx s t s' ENTRY MDL EXEC UT) as POST.
  split. exact (proj1 POST).
  assert (MEM: s' V_MEM32 = s V_MEM32)
    by (apply (proj2 POST); discriminate).
  intro a. rewrite MEM. reflexivity.
Qed.

Theorem tick_count_isr_return_step : forall s
  (ODD: N.odd (s R_LR) = true) (NORMAL: s R_LR < 0xfffffff0),
  can_step xTaskGetTickCountFromISR_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s),(Addr 0x594,s)).
Proof.
  intros s ODD NORMAL.
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
  assert (CS: can_step xTaskGetTickCountFromISR_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),reset_temps s s),(Addr 0x594,s))).
  { eapply CanStep with (sz:=2) (q:=armv6m_bxwritepc (Var R_LR))
      (x:=Some (Addr (N.land (s R_LR) (N.ones 32 - 1))));
      [reflexivity | exact XS]. }
  assert (RESET: reset_temps s s = s).
  { extensionality v. destruct v; reflexivity. }
  rewrite RESET in CS. exact CS.
Qed.

Corollary tick_count_isr_caller_result : forall s t s'
  (ENTRY: startof t (Addr 0x594,s') = (Addr 0x590,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog xTaskGetTickCountFromISR_armv6m_prog ((Addr 0x594,s')::t))
  (UT: unterminated tick_count_isr_exit t)
  (ODD: N.odd (s R_LR) = true)
  (NORMAL: s R_LR < 0xfffffff0),
  tick_count_isr_postcondition s s' /\
  can_step xTaskGetTickCountFromISR_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32 - 1)),s'),(Addr 0x594,s')).
Proof.
  intros.
  pose proof (tick_count_isr_post_at_bx s t s' ENTRY MDL EXEC UT) as POST.
  assert (LR: s' R_LR = s R_LR) by (apply (proj2 POST); discriminate).
  split. exact POST.
  rewrite <- LR. apply tick_count_isr_return_step.
  - rewrite LR. exact ODD.
  - rewrite LR. exact NORMAL.
Qed.
