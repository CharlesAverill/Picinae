(* vTaskMissedYield -- set the actual yield-pending word, sequential ARMv6-M IL.

   Initial author: OpenAI gpt-6-astra, xhigh, default, one-shot (r11-missed-yield).
   Repair and final proof producer: OpenAI gpt-6.1-sol, xhigh/default.
   Original evidence: notes/r11-missed-yield; validation: notes/r11-missed-yield-fix.
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
Proof. exact vTaskMissedYield_armv6m_welltyped. Qed.
Theorem missed_yield_nwc : forall s1 s2,
  vTaskMissedYield_armv6m_prog s1 = vTaskMissedYield_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem missed_yield_memory_word : forall s,
  (missed_yield_memory s) Ⓓ[0x2000001c] = 1.
Proof.
  intro s. unfold missed_yield_memory.
  rewrite getmem_setmem by discriminate. reflexivity.
Qed.
Theorem missed_yield_memory_bytes : forall s,
  (missed_yield_memory s) Ⓑ[0x2000001c] = 1 /\
  (missed_yield_memory s) Ⓑ[0x2000001d] = 0 /\
  (missed_yield_memory s) Ⓑ[0x2000001e] = 0 /\
  (missed_yield_memory s) Ⓑ[0x2000001f] = 0.
Proof.
  (* Split only conjunctions: trying equality constructors here unfolds the
     integer memory representation at a large address and exhausts the cap. *)
  intro s. unfold missed_yield_memory. split; [|split; [|split]].
  - exact (getmem_setmem_xbits 32 LittleE 1 0 3 (s V_MEM32) 0x2000001c 1 ltac:(discriminate)).
  - exact (getmem_setmem_xbits 32 LittleE 1 1 2 (s V_MEM32) 0x2000001c 1 ltac:(discriminate)).
  - exact (getmem_setmem_xbits 32 LittleE 1 2 1 (s V_MEM32) 0x2000001c 1 ltac:(discriminate)).
  - exact (getmem_setmem_xbits 32 LittleE 1 3 0 (s V_MEM32) 0x2000001c 1 ltac:(discriminate)).
Qed.
Theorem missed_yield_memory_outside : forall s a,
  ~ overlap 32 a 1 0x2000001c 4 ->
  (missed_yield_memory s) Ⓑ[a] = (s V_MEM32) Ⓑ[a].
Proof. intros s a NO. unfold missed_yield_memory. apply getmem_noverlap, NO. Qed.

Theorem missed_yield_preserves_registers : forall v,
  v <> V_MEM32 -> v <> R_R2 -> v <> R_R3 -> v <> F_N -> v <> F_Z ->
  forall_endstates vTaskMissedYield_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof.
  intros v MEM R2 R3 FN FZ. apply noassign_prog_same.
  intros s a. unfold vTaskMissedYield_armv6m_prog.
  destruct (existsb (N.eqb a) vTaskMissedYield_armv6m_entries) eqn:IN; [|exact I].
  apply existsb_exists in IN. destruct IN as [b [IN EQ]].
  apply N.eqb_eq in EQ. subst a.
  change (0x9c0 = b \/ 0x9c2 = b \/ 0x9c4 = b \/ 0x9c6 = b \/ False) in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]];
    hnf;
    lazymatch goal with |- allassigns ?P ?q =>
      let Q := eval vm_compute in q in change (allassigns P Q)
    end;
    repeat constructor; congruence.
Qed.

Theorem missed_yield_correct : forall s t s' x'
  (ENTRY: startof t (x',s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s),
  satisfies_all vTaskMissedYield_armv6m_prog
    (missed_yield_invariants s) missed_yield_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. armv6m_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply missed_yield_welltyped. intro MDL1.
    clear - PRE MDL1. destruct_inv 32 PRE.
    subst s1. repeat armv6m_step.
    unfold missed_yield_postcondition, missed_yield_memory.
    repeat split; try reflexivity.
    unfold missed_yield_register_frame. intros v MEM R2 R3 FN FZ.
    repeat rewrite update_frame by assumption. reflexivity.
Qed.

Corollary missed_yield_post_at_bx : forall s t s'
  (ENTRY: startof t (Addr 0x9c6,s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog vTaskMissedYield_armv6m_prog ((Addr 0x9c6,s')::t))
  (UT: unterminated missed_yield_exit t),
  missed_yield_postcondition s s'.
Proof.
  intros. exact (satall_trueif_inv _ _ _ _
    (missed_yield_correct s t s' (Addr 0x9c6) ENTRY MDL) EXEC UT).
Qed.

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
Proof.
  intros. pose proof (proj1 (missed_yield_post_at_bx s t s' ENTRY MDL EXEC UT)) as MEM.
  split; [rewrite MEM; apply missed_yield_memory_word|]. split.
  - rewrite MEM. apply missed_yield_memory_bytes.
  - intros a NO. rewrite MEM. apply missed_yield_memory_outside, NO.
Qed.
Corollary missed_yield_preserves_callee_saved : forall s t s'
  (ENTRY: startof t (Addr 0x9c6,s') = (Addr 0x9c0,s))
  (MDL: models armv6mtypctx s)
  (EXEC: exec_prog vTaskMissedYield_armv6m_prog ((Addr 0x9c6,s')::t))
  (UT: unterminated missed_yield_exit t),
  forall v, In v [R_R4;R_R5;R_R6;R_R7;R_R8;R_R9;R_R10;R_R11;R_SP;R_LR] ->
    s' v = s v.
Proof.
  intros s t s' ENTRY MDL EXEC UT v IN.
  destruct (missed_yield_post_at_bx s t s' ENTRY MDL EXEC UT)
    as [_ [_ [_ [_ [_ FRAME]]]]].
  apply FRAME; intro EQ; subst v; cbn in IN; intuition discriminate.
Qed.

Lemma missed_yield_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.
Definition missed_yield_entry_store (m lr:N) : store := fun v =>
  match v with V_MEM32 => m | A_WRITE => N.ones (2^32) | R_LR => lr | _ => 0 end.
Theorem missed_yield_entry_satisfiable : forall m lr,
  m < 2^(8*2^32) -> missed_yield_ordinary_lr lr ->
  exists s, missed_yield_entry s /\ s V_MEM32 = m /\ s R_LR = lr.
Proof.
  intros m lr B LR. exists (missed_yield_entry_store m lr).
  split; [|split; reflexivity]. split.
  - intros v w T. destruct v; cbn [armv6mtypctx] in T;
      try discriminate; injection T as <-.
    all: lazymatch goal with
    | |- missed_yield_entry_store _ _ V_MEM32 < _ => exact B
    | |- missed_yield_entry_store _ _ A_WRITE < _ => exact (ones_bound (2^32))
    | |- missed_yield_entry_store _ _ R_LR < _ =>
        change (lr < 2^32); eapply N.lt_trans; [exact (proj1 LR)|reflexivity]
    | |- _ < 2^?width => exact (missed_yield_zero_bound width)
    end.
  - split; [|exact LR]. intros i I. unfold mem_writable.
    change (N.testbit (N.ones (2^32)) ((0x2000001c+i) mod 2^32) = true).
    apply N.ones_spec_low. apply N.mod_lt, pow2_nonzero.
Qed.

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
Proof.
  intro s. unfold missed_yield_after_ldr.
  eapply CanStep with (a:=0x9c0) (sz:=2) (x:=None); [reflexivity|].
  apply XMove. constructor.
Qed.
Theorem missed_yield_mov_step : forall s,
  can_step vTaskMissedYield_armv6m_prog
    ((Addr 0x9c4,missed_yield_after_mov s),(Addr 0x9c2,missed_yield_after_ldr s)).
Proof.
  intro s. unfold missed_yield_after_mov.
  eapply CanStep with (a:=0x9c2) (sz:=2) (x:=None); [reflexivity|].
  eapply XSeq2.
  - eapply XSeq2.
    + apply XMove with (n:=0) (w:=1).
      change (eval_exp armv6mtypctx (missed_yield_after_ldr s)
        (Cast CAST_HIGH 1 (Word 1 32)) (cast CAST_HIGH 32 1 1) 1).
      apply ECast. constructor.
    + apply XMove with (n:=0) (w:=1).
      apply EBinOp with (n1:=1) (n2:=0) (w:=32); constructor.
  - apply XMove. constructor.
Qed.
Theorem missed_yield_store_step : forall s, missed_yield_writable s ->
  can_step vTaskMissedYield_armv6m_prog
    ((Addr 0x9c6,missed_yield_after_store s),(Addr 0x9c4,missed_yield_after_mov s)).
Proof.
  intros s WR. unfold missed_yield_after_store, missed_yield_memory.
  eapply CanStep with (a:=0x9c4) (sz:=2) (x:=None); [reflexivity|].
  apply XMove. eapply EStore.
  - change (eval_exp armv6mtypctx (missed_yield_after_mov s) (Var V_MEM32)
      (missed_yield_after_mov s V_MEM32) (2^32*8)). apply EVar. reflexivity.
  - change (eval_exp armv6mtypctx (missed_yield_after_mov s)
      (BinOp OP_PLUS (Var R_R3) (Word 0 32))
      (eval_binop OP_PLUS 32 (missed_yield_after_mov s R_R3) 0) 32).
    apply EBinOp; [apply EVar; reflexivity|constructor].
  - change (eval_exp armv6mtypctx (missed_yield_after_mov s) (Var R_R2)
      (missed_yield_after_mov s R_R2) 32). apply EVar. reflexivity.
  - intros i I. change (mem_writable s ((0x2000001c+i) mod 2^32)). apply WR, I.
Qed.
Theorem missed_yield_execution_witness : forall s, missed_yield_entry s ->
  exec_prog vTaskMissedYield_armv6m_prog
    [(Addr 0x9c6,missed_yield_after_store s); (Addr 0x9c4,missed_yield_after_mov s);
     (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)] /\
  missed_yield_postcondition s (missed_yield_after_store s).
Proof.
  intros s ENTRY.
  assert (XP: exec_prog vTaskMissedYield_armv6m_prog
    [(Addr 0x9c6,missed_yield_after_store s); (Addr 0x9c4,missed_yield_after_mov s);
     (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)]).
  { apply exec_prog_step.
    - apply exec_prog_step.
      + apply exec_prog_step; [apply exec_prog_none|apply missed_yield_ldr_step].
      + apply missed_yield_mov_step.
    - apply missed_yield_store_step. exact (proj1 (proj2 ENTRY)). }
  split; [exact XP|].
  exact (missed_yield_post_at_bx s
    [(Addr 0x9c4,missed_yield_after_mov s); (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)]
    (missed_yield_after_store s) eq_refl (proj1 ENTRY) XP ltac:(repeat constructor)).
Qed.

Theorem missed_yield_return_step : forall s,
  missed_yield_ordinary_lr (s R_LR) ->
  can_step vTaskMissedYield_armv6m_prog
    ((Addr (N.land (s R_LR) (N.ones 32-1)),s),(Addr 0x9c6,s)).
Proof.
  intros s [BOUND ODD].
  assert (LOW: s R_LR mod 2 = 1).
  { apply mod2_1_neven. rewrite <- N.negb_odd, ODD. reflexivity. }
  assert (RST: reset_temps s s = s).
  { extensionality v. destruct v; reflexivity. }
  rewrite <- RST at 2.
  eapply CanStep with (a:=0x9c6) (sz:=2) (x:=Some (Addr (N.land (s R_LR) (N.ones 32-1))));
    [reflexivity|].
  eapply XIf with (b:=1).
  - assert (E: eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR))
        (s R_LR mod 2) 1).
    { change (eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR))
        (cast CAST_LOW 32 1 (s R_LR)) 1).
      apply ECast. apply EVar. reflexivity. }
    rewrite LOW in E. exact E.
  - apply XJmp with (w:=32).
    apply EBinOp with (n1:=s R_LR) (n2:=N.ones 32-1) (w:=32);
      [apply EVar; reflexivity|constructor].
Qed.
Corollary missed_yield_execution_returns : forall s, missed_yield_entry s ->
  exec_prog vTaskMissedYield_armv6m_prog
    [(Addr (N.land (s R_LR) (N.ones 32-1)),missed_yield_after_store s);
     (Addr 0x9c6,missed_yield_after_store s); (Addr 0x9c4,missed_yield_after_mov s);
     (Addr 0x9c2,missed_yield_after_ldr s); (Addr 0x9c0,s)].
Proof.
  intros s ENTRY. apply exec_prog_step.
  - exact (proj1 (missed_yield_execution_witness s ENTRY)).
  - change (can_step vTaskMissedYield_armv6m_prog
      ((Addr (N.land (missed_yield_after_store s R_LR) (N.ones 32-1)),missed_yield_after_store s),
       (Addr 0x9c6,missed_yield_after_store s))).
    apply missed_yield_return_step. exact (proj2 (proj2 ENTRY)).
Qed.
