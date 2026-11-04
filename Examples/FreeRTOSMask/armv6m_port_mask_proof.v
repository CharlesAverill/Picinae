(* FreeRTOS V11.1.0 Cortex-M0 port mask callees.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, r42-port-mask.
   Proof repair/completion: OpenAI gpt-6.1-sol, xhigh/priority,
   r42-port-mask-fix. All original definitions and statements retained.
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
Proof.
  intros s MDL. unfold mask_set_postcondition. split; [|split; [|split]].
  - unfold mask_set_result, mask_set_mrs. rewrite update_frame by discriminate.
    apply update_updated.
  - apply update_updated.
  - unfold mask_set_result, mask_set_mrs. rewrite update_frame by discriminate.
    rewrite update_updated. exact (MDL S_PRIMASK 1 eq_refl).
  - apply mask_set_result_frame.
Qed.
Theorem mask_clear_result_post : forall s,
  mask_clear_postcondition s (mask_clear_result s).
Proof. intro s. split; [apply update_updated | apply mask_clear_result_frame]. Qed.

(* A typed starting store exists for every supported memory/argument/SP. *)
Definition mask_input_store m arg sp : store :=
  update (update (update (fun _ => 0) V_MEM32 m) R_R0 arg) R_SP sp.
Theorem mask_input_store_typed : forall m arg sp,
  m < 2^(8*2^32) -> arg < 2^32 -> sp < 2^32 ->
  models armv6mtypctx (mask_input_store m arg sp).
Proof.
  intros m arg sp M A S. unfold mask_input_store.
  apply models_update; [exact S |].
  apply models_update; [exact A |].
  apply models_update; [exact M |].
  intros v w T. assert (NZ: 2^w <> 0) by (apply N.pow_nonzero; discriminate).
  cbn. clear - NZ. lia.
Qed.

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
Proof.
  intros s p h lr MDL P H ODD LR.
  assert (MDL': models armv6mtypctx (mask_entry_store s p h lr)).
  { unfold mask_entry_store.
    apply models_update; [cbn [armv6mtypctx]; clear - LR; lia |].
    apply models_update; [reflexivity |].
    apply models_update; [exact H |].
    apply models_update; [exact P | exact MDL]. }
  split.
  - unfold mask_entry. split; [exact MDL' |].
    unfold mask_entry_store. repeat rewrite update_frame by discriminate.
    repeat rewrite update_updated. repeat split; assumption.
  - unfold mask_entry_store. repeat rewrite update_frame by discriminate.
    rewrite update_updated. repeat split; reflexivity.
Qed.
Theorem mask_both_bits_inhabited : forall s h lr,
  models armv6mtypctx s -> h < 2 -> N.odd lr = true -> lr < 0xfffffff0 ->
  mask_entry (mask_entry_store s 0 h lr) /\
  mask_entry (mask_entry_store s 1 h lr).
Proof. intros s h lr M H O L. split.
  - exact (proj1 (mask_entry_witness s 0 h lr M ltac:(lia) H O L)).
  - exact (proj1 (mask_entry_witness s 1 h lr M ltac:(lia) H O L)).
Qed.

Lemma mask_reset_same : forall s, reset_temps s s = s.
Proof. intro s. apply functional_extensionality. intro v.
  unfold reset_temps, reset_vars. destruct (archtyps v); reflexivity. Qed.
Lemma mask_reset_update : forall s v n w, armv6mtypctx v = Some w ->
  reset_temps s (update s v n) = update s v n.
Proof.
  intros s v n w T. apply functional_extensionality. intro u.
  destruct (Var.eq_dec u v) as [->|NE].
  - unfold reset_temps, reset_vars. change (armv6mtypctx v) with (archtyps v) in T.
    rewrite T. reflexivity.
  - unfold reset_temps, reset_vars. destruct (archtyps u);
      rewrite !update_frame by exact NE; reflexivity.
Qed.

Definition mask_mrs_stmt := Move R_R0 armv6m_read_primask.
Definition mask_cps_stmt := armv6m_write_primask (Word 1 1).
Definition mask_msr_stmt := armv6m_write_primask (Cast CAST_LOW 1 (Var R_R0)).
Definition mask_bx_stmt := armv6m_bxwritepc (Var R_LR).

Lemma mask_set_lookup_mrs : forall s, s S_CONTROL_NPRIV = 0 ->
  ulSetInterruptMask_prog s 0x4090 = Some (4,mask_mrs_stmt).
Proof. intros s H. change ((if s S_CONTROL_NPRIV =? 0 then
  Some (4,mask_mrs_stmt) else None) = Some (4,mask_mrs_stmt)). rewrite H. reflexivity. Qed.
Lemma mask_set_lookup_cps : forall s, s S_CONTROL_NPRIV = 0 ->
  ulSetInterruptMask_prog s 0x4094 = Some (2,mask_cps_stmt).
Proof. intros s H. change ((if s S_CONTROL_NPRIV =? 0 then
  Some (2,mask_cps_stmt) else None) = Some (2,mask_cps_stmt)). rewrite H. reflexivity. Qed.
Lemma mask_clear_lookup_msr : forall s, s S_CONTROL_NPRIV = 0 ->
  vClearInterruptMask_prog s 0x4098 = Some (4,mask_msr_stmt).
Proof. intros s H. change ((if s S_CONTROL_NPRIV =? 0 then
  Some (4,mask_msr_stmt) else None) = Some (4,mask_msr_stmt)). rewrite H. reflexivity. Qed.
Lemma mask_set_lookup_bx : forall s, s S_CONTROL_NPRIV = 0 ->
  s R_LR < 0xfffffff0 -> ulSetInterruptMask_prog s 0x4096 = Some (2,mask_bx_stmt).
Proof. intros s H L. change ((if s S_CONTROL_NPRIV =? 0 then
  if s R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None else None) = Some (2,mask_bx_stmt)).
  rewrite H, (proj2 (N.ltb_lt _ _) L). reflexivity. Qed.
Lemma mask_clear_lookup_bx : forall s, s S_CONTROL_NPRIV = 0 ->
  s R_LR < 0xfffffff0 -> vClearInterruptMask_prog s 0x409c = Some (2,mask_bx_stmt).
Proof. intros s H L. change ((if s S_CONTROL_NPRIV =? 0 then
  if s R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None else None) = Some (2,mask_bx_stmt)).
  rewrite H, (proj2 (N.ltb_lt _ _) L). reflexivity. Qed.

(* Conditional nwc, including stores outside the supported profile. *)
Theorem mask_set_code_stable : forall s t,
  s S_CONTROL_NPRIV = t S_CONTROL_NPRIV -> s R_LR = t R_LR ->
  forall a, ulSetInterruptMask_prog s a = ulSetInterruptMask_prog t a.
Proof.
  intros s t C L a. unfold ulSetInterruptMask_prog, armv6m_base_profile.
  rewrite C. destruct (t S_CONTROL_NPRIV =? 0); [|reflexivity].
  destruct (existsb (N.eqb a) ulSetInterruptMask_entries) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as [b [IN EQ]]. apply N.eqb_eq in EQ.
  subst a. cbn [ulSetInterruptMask_entries] in IN.
  destruct IN as [<-|[<-|[<-|[]]]]; try reflexivity.
  change ((if s R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None) =
               (if t R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None)); now rewrite L.
Qed.
Theorem mask_clear_code_stable : forall s t,
  s S_CONTROL_NPRIV = t S_CONTROL_NPRIV -> s R_LR = t R_LR ->
  forall a, vClearInterruptMask_prog s a = vClearInterruptMask_prog t a.
Proof.
  intros s t C L a. unfold vClearInterruptMask_prog, armv6m_base_profile.
  rewrite C. destruct (t S_CONTROL_NPRIV =? 0); [|reflexivity].
  destruct (existsb (N.eqb a) vClearInterruptMask_entries) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as [b [IN EQ]]. apply N.eqb_eq in EQ.
  subst a. cbn [vClearInterruptMask_entries] in IN.
  destruct IN as [<-|[<-|[]]]; try reflexivity.
  change ((if s R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None) =
          (if t R_LR <? 0xfffffff0 then Some (2,mask_bx_stmt) else None)); now rewrite L.
Qed.

Lemma mask_privileged_eval : forall s, models armv6mtypctx s ->
  s S_CONTROL_NPRIV = 0 -> eval_exp armv6mtypctx s armv6m_privileged 1 1.
Proof.
  intros s MDL C. pose proof (MDL S_HANDLER 1 eq_refl) as H.
  assert (B: s S_HANDLER = 0 \/ s S_HANDLER = 1) by (change (s S_HANDLER < 2) in H; clear - H; lia).
  assert (E: eval_exp armv6mtypctx s armv6m_privileged
    (eval_binop OP_OR 1 (s S_HANDLER)
      (eval_unop OP_NOT (s S_CONTROL_NPRIV) 1)) 1).
  { apply EBinOp; [apply EVar; reflexivity | apply EUnOp; apply EVar; reflexivity]. }
  rewrite C in E. destruct B as [B|B]; rewrite B in E; exact E.
Qed.
Lemma mask_mrs_exec : forall s, models armv6mtypctx s -> s S_CONTROL_NPRIV = 0 ->
  exec_stmt armv6mtypctx s mask_mrs_stmt (update armv6mtypctx R_R0 (Some 32))
    (mask_set_mrs s) None.
Proof.
  intros s M C. apply XMove. unfold armv6m_read_primask.
  change (eval_exp armv6mtypctx s (Cast CAST_UNSIGNED 32
    (Ite armv6m_privileged (Var S_PRIMASK) (Word 0 1)))
    (cast CAST_UNSIGNED 1 32 (s S_PRIMASK)) 32).
  apply ECast. change (eval_exp armv6mtypctx s
    (Ite armv6m_privileged (Var S_PRIMASK) (Word 0 1))
    (match 1 with 0 => 0 | _ => s S_PRIMASK end) 1).
  eapply EIte; [apply mask_privileged_eval; assumption | apply EVar; reflexivity | apply EWord].
Qed.
Lemma mask_write_exec : forall s e n, models armv6mtypctx s ->
  s S_CONTROL_NPRIV = 0 -> eval_exp armv6mtypctx s e n 1 ->
  exec_stmt armv6mtypctx s (armv6m_write_primask e)
    (update armv6mtypctx S_PRIMASK (Some 1)) (update s S_PRIMASK n) None.
Proof. intros s e n M C E. eapply XIf with (b:=1).
  - apply mask_privileged_eval; assumption.
  - apply XMove, E.
Qed.
Lemma mask_bx_exec : forall s, N.odd (s R_LR) = true ->
  exec_stmt armv6mtypctx s mask_bx_stmt armv6mtypctx s (Some (Addr (mask_return s))).
Proof.
  intros s O. assert (BIT: s R_LR mod 2 = 1).
  { rewrite <- N.bit0_mod, N.bit0_odd, O. reflexivity. }
  eapply XIf with (b:=1).
  - change (eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR)) 1 1).
    assert (E: eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR))
      (s R_LR mod 2) 1).
    { change (eval_exp armv6mtypctx s (Cast CAST_LOW 1 (Var R_LR))
        (cast CAST_LOW 32 1 (s R_LR)) 1). eapply ECast with (w:=32); apply EVar; reflexivity. }
    now rewrite BIT in E.
  - eapply XJmp with (w:=32). eapply EBinOp with (n1:=s R_LR) (n2:=N.ones 32 - 1) (w:=32);
      [apply EVar; reflexivity | apply EWord].
Qed.

Lemma mask_move_step : forall p a sz s v n w e,
  p s a = Some (sz,Move v e) -> armv6mtypctx v = Some w ->
  eval_exp armv6mtypctx s e n w ->
  can_step p ((Addr (a+sz),update s v n),(Addr a,s)).
Proof. intros. rewrite <- (mask_reset_update s v n w H0).
  eapply CanStep with (x:=None); [exact H | apply XMove; exact H1]. Qed.
Lemma mask_return_step : forall p a s,
  p s a = Some (2,mask_bx_stmt) -> N.odd (s R_LR) = true ->
  can_step p ((Addr (mask_return s),s),(Addr a,s)).
Proof.
  intros p a s LU O.
  pose proof (CanStep p a s 2 mask_bx_stmt armv6mtypctx s
    (Some (Addr (mask_return s))) LU (mask_bx_exec s O)) as CS.
  cbn [exitof] in CS. rewrite mask_reset_same in CS. exact CS.
Qed.
Lemma mask_step_unique : forall p a s sz q c' s' x,
  p s a = Some (sz,q) -> forall_exps_in_stmt not_unknown q ->
  exec_stmt armv6mtypctx s q c' s' x -> forall z,
  can_step p (z,(Addr a,s)) -> z = (exitof (a+sz) x,reset_temps s s').
Proof.
  intros p a s sz q c' s' x LU NU X z CS. inversion CS; subst.
  match goal with H: p s a = Some _ |- _ => rewrite LU in H; inversion H; subst end.
  match goal with H: exec_stmt _ _ _ _ _ _ |- _ =>
    pose proof (exec_stmt_deterministic NU X H) as EQ end.
  inversion EQ; subst; reflexivity.
Qed.

Theorem mask_set_execution : forall s, mask_entry s ->
  can_step ulSetInterruptMask_prog ((Addr 0x4094,mask_set_mrs s),(Addr 0x4090,s)) /\
  can_step ulSetInterruptMask_prog ((Addr 0x4096,mask_set_result s),(Addr 0x4094,mask_set_mrs s)) /\
  can_step ulSetInterruptMask_prog ((Addr (mask_return s),mask_set_result s),(Addr 0x4096,mask_set_result s)) /\
  mask_set_postcondition s (mask_set_result s).
Proof.
  intros s [M [C [O L]]].
  assert (M1: models armv6mtypctx (mask_set_mrs s)).
  { apply models_update; [pose proof (M S_PRIMASK 1 eq_refl) as B; change (s S_PRIMASK < 2) in B; cbn [armv6mtypctx]; clear - B; lia | exact M]. }
  assert (C1: mask_set_mrs s S_CONTROL_NPRIV = 0) by
    (unfold mask_set_mrs; rewrite update_frame by discriminate; exact C).
  split.
  - unfold mask_set_mrs at 1. rewrite <- (mask_reset_update s R_R0 (s S_PRIMASK) 32 eq_refl).
    eapply CanStep with (a:=0x4090) (sz:=4) (x:=None); [apply mask_set_lookup_mrs, C | apply mask_mrs_exec; assumption].
  - split.
    + unfold mask_set_result. rewrite <- (mask_reset_update (mask_set_mrs s) S_PRIMASK 1 1 eq_refl).
      eapply CanStep with (a:=0x4094) (sz:=2) (x:=None); [apply mask_set_lookup_cps, C1 | apply mask_write_exec; auto; apply EWord].
    + split.
      * replace (mask_return s) with (mask_return (mask_set_result s)) by
      (unfold mask_return; rewrite mask_set_result_frame by discriminate; reflexivity).
        apply mask_return_step.
        -- apply mask_set_lookup_bx; rewrite mask_set_result_frame by discriminate; assumption.
        -- rewrite mask_set_result_frame by discriminate; assumption.
      * apply (mask_set_result_post s M).
Qed.
Theorem mask_clear_execution : forall s, mask_entry s ->
  can_step vClearInterruptMask_prog ((Addr 0x409c,mask_clear_result s),(Addr 0x4098,s)) /\
  can_step vClearInterruptMask_prog ((Addr (mask_return s),mask_clear_result s),(Addr 0x409c,mask_clear_result s)) /\
  mask_clear_postcondition s (mask_clear_result s).
Proof.
  intros s [M [C [O L]]]. split.
  - unfold mask_clear_result. rewrite <- (mask_reset_update s S_PRIMASK (s R_R0 mod 2) 1 eq_refl).
    eapply CanStep with (a:=0x4098) (sz:=4) (x:=None); [apply mask_clear_lookup_msr, C |].
    apply mask_write_exec; try assumption. eapply ECast with (ct:=CAST_LOW) (w:=32) (w':=1) (n:=s R_R0); apply EVar; reflexivity.
  - split.
    + replace (mask_return s) with (mask_return (mask_clear_result s)) by
      (unfold mask_return; rewrite mask_clear_result_frame by discriminate; reflexivity).
      apply mask_return_step.
      * apply mask_clear_lookup_bx; rewrite mask_clear_result_frame by discriminate; assumption.
      * rewrite mask_clear_result_frame by discriminate; assumption.
    + apply mask_clear_result_post.
Qed.

(* Universal completed-step specifications, paired above with concrete paths.
   No desired result, callee contract, or assumed execution oracle is a premise. *)
Theorem ulSetInterruptMask_correct : forall s s1 s2 s3 x1 x2 x3,
  mask_entry s ->
  can_step ulSetInterruptMask_prog ((x1,s1),(Addr 0x4090,s)) ->
  can_step ulSetInterruptMask_prog ((x2,s2),(x1,s1)) ->
  can_step ulSetInterruptMask_prog ((x3,s3),(x2,s2)) ->
  x3 = Addr (mask_return s) /\ s3 = mask_set_result s /\ mask_set_postcondition s s3.
Proof.
  intros s s1 s2 s3 x1 x2 x3 PRE X1 X2 X3.
  destruct PRE as [M [C [O L]]].
  pose proof (mask_step_unique _ _ _ _ _ _ _ _ (mask_set_lookup_mrs s C)
    ltac:(repeat split) (mask_mrs_exec s M C) _ X1) as E1.
  unfold mask_set_mrs in E1. rewrite (mask_reset_update _ R_R0 _ 32 eq_refl) in E1. inversion E1; subst x1 s1.
  assert (M1: models armv6mtypctx (mask_set_mrs s)) by
    (apply models_update; [pose proof (M S_PRIMASK 1 eq_refl) as B; change (s S_PRIMASK < 2) in B; cbn [armv6mtypctx]; clear - B; lia | exact M]).
  assert (C1: mask_set_mrs s S_CONTROL_NPRIV = 0) by
    (unfold mask_set_mrs; rewrite update_frame by discriminate; exact C).
  pose proof (mask_write_exec (mask_set_mrs s) (Word 1 1) 1 M1 C1 (EWord _ _ 1 1)) as W.
  pose proof (mask_step_unique _ _ _ _ _ _ _ _ (mask_set_lookup_cps _ C1)
    ltac:(repeat split) W _ X2) as E2.
  rewrite (mask_reset_update _ S_PRIMASK _ 1 eq_refl) in E2. inversion E2; subst x2 s2.
  assert (C2: mask_set_result s S_CONTROL_NPRIV = 0) by
    (rewrite mask_set_result_frame by discriminate; exact C).
  assert (O2: N.odd (mask_set_result s R_LR) = true) by
    (rewrite mask_set_result_frame by discriminate; exact O).
  assert (L2: mask_set_result s R_LR < 0xfffffff0) by
    (rewrite mask_set_result_frame by discriminate; exact L).
  pose proof (mask_step_unique _ _ _ _ _ _ _ _ (mask_set_lookup_bx _ C2 L2)
    ltac:(repeat split) (mask_bx_exec _ O2) _ X3) as E3.
  rewrite mask_reset_same in E3. inversion E3; subst x3 s3.
  split.
  - unfold mask_return. rewrite mask_set_result_frame by discriminate. reflexivity.
  - split; [reflexivity | apply mask_set_result_post, M].
Qed.
Theorem vClearInterruptMask_correct : forall s s1 s2 x1 x2,
  mask_entry s ->
  can_step vClearInterruptMask_prog ((x1,s1),(Addr 0x4098,s)) ->
  can_step vClearInterruptMask_prog ((x2,s2),(x1,s1)) ->
  x2 = Addr (mask_return s) /\ s2 = mask_clear_result s /\ mask_clear_postcondition s s2.
Proof.
  intros s s1 s2 x1 x2 [M [C [O L]]] X1 X2.
  assert (W: exec_stmt armv6mtypctx s mask_msr_stmt
    (update armv6mtypctx S_PRIMASK (Some 1)) (mask_clear_result s) None).
  { apply mask_write_exec; try assumption. eapply ECast with (ct:=CAST_LOW) (w:=32) (w':=1) (n:=s R_R0); apply EVar; reflexivity. }
  pose proof (mask_step_unique _ _ _ _ _ _ _ _ (mask_clear_lookup_msr _ C)
    ltac:(repeat split) W _ X1) as E1.
  unfold mask_clear_result in E1. rewrite (mask_reset_update _ S_PRIMASK _ 1 eq_refl) in E1. inversion E1; subst x1 s1.
  assert (C1: mask_clear_result s S_CONTROL_NPRIV = 0) by
    (rewrite mask_clear_result_frame by discriminate; exact C).
  assert (O1: N.odd (mask_clear_result s R_LR) = true) by
    (rewrite mask_clear_result_frame by discriminate; exact O).
  assert (L1: mask_clear_result s R_LR < 0xfffffff0) by
    (rewrite mask_clear_result_frame by discriminate; exact L).
  pose proof (mask_step_unique _ _ _ _ _ _ _ _ (mask_clear_lookup_bx _ C1 L1)
    ltac:(repeat split) (mask_bx_exec _ O1) _ X2) as E2.
  rewrite mask_reset_same in E2. inversion E2; subst x2 s2.
  split.
  - unfold mask_return. rewrite mask_clear_result_frame by discriminate. reflexivity.
  - split; [reflexivity | apply mask_clear_result_post].
Qed.

(* Floyd-Hoare interface to the return-instruction cut. The separate execution
   and completed-step theorems above include BX, including its dynamic guard. *)
Theorem ulSetInterruptMask_satisfies_all : forall s t s' x',
  startof t (x',s') = (Addr 0x4090,s) -> mask_entry s ->
  satisfies_all ulSetInterruptMask_prog (mask_set_invs s) mask_set_exit ((x',s')::t).
Proof.
  intros s t s' x' ENTRY PRE0. apply prove_invs.
  - simpl. rewrite ENTRY. apply NIHere. simpl. split; [reflexivity | exact PRE0].
  - intros t1 a1 s1 t2 UT SPL PRE.
    unfold get_precondition in PRE.
    destruct (mask_set_exit ((Addr a1,s1)::t1)) eqn:EX; [contradiction |].
    destruct (ulSetInterruptMask_prog s1 a1) eqn:LU; [|contradiction].
    (* Enumerate only the invariant map. Expanding the state-dependent
       instruction decoder at every address prefix exhausts the memory cap. *)
    assert (PRE': true_inv (get_precondition (fun (_:store) (_:addr) => Some tt)
      (mask_set_invs s) mask_set_exit a1 s1 t1)).
    { unfold get_precondition. rewrite EX. exact PRE. }
    clear PRE LU EX. rename PRE' into PRE. destruct_inv 32 PRE.
    destruct PRE as [EQ PRE]. subst s1. destruct PRE as [M [C [O L]]].
    eapply NIStep with (sz:=4) (q:=mask_mrs_stmt).
    + unfold effinv, effinv'. cbn [mask_set_invs mask_set_exit].
      rewrite mask_set_lookup_mrs by exact C. reflexivity.
    + apply mask_set_lookup_mrs, C.
    + intros c1 s1 x1 XS.
      pose proof (exec_stmt_deterministic (q:=mask_mrs_stmt) ltac:(repeat split) (mask_mrs_exec s M C) XS) as EQ.
      inversion EQ; subst. unfold mask_set_mrs. rewrite (mask_reset_update _ R_R0 _ 32 eq_refl).
      assert (M1: models armv6mtypctx (mask_set_mrs s)) by
        (apply models_update; [pose proof (M S_PRIMASK 1 eq_refl) as B; change (s S_PRIMASK < 2) in B; cbn [armv6mtypctx]; clear - B; lia | exact M]).
      assert (C1: mask_set_mrs s S_CONTROL_NPRIV = 0) by
        (unfold mask_set_mrs; rewrite update_frame by discriminate; exact C).
      eapply NIStep with (sz:=2) (q:=mask_cps_stmt).
      * unfold effinv, effinv'. cbn [mask_set_invs mask_set_exit].
        rewrite mask_set_lookup_cps by exact C1. reflexivity.
      * apply mask_set_lookup_cps, C1.
      * intros c2 s2 x2 XS2.
        pose proof (mask_write_exec (mask_set_mrs s) (Word 1 1) 1 M1 C1 (EWord _ _ 1 1)) as W.
        pose proof (exec_stmt_deterministic (q:=mask_cps_stmt) ltac:(repeat split) W XS2) as EQ2.
        inversion EQ2; subst. rewrite (mask_reset_update _ S_PRIMASK _ 1 eq_refl).
        apply NIHere. change (mask_set_result s = mask_set_result s /\
          mask_set_postcondition s (mask_set_result s)).
        split; [reflexivity | apply mask_set_result_post, M].
Qed.
Theorem vClearInterruptMask_satisfies_all : forall s t s' x',
  startof t (x',s') = (Addr 0x4098,s) -> mask_entry s ->
  satisfies_all vClearInterruptMask_prog (mask_clear_invs s) mask_clear_exit ((x',s')::t).
Proof.
  intros s t s' x' ENTRY PRE0. apply prove_invs.
  - simpl. rewrite ENTRY. apply NIHere. simpl. split; [reflexivity | exact PRE0].
  - intros t1 a1 s1 t2 UT SPL PRE.
    unfold get_precondition in PRE.
    destruct (mask_clear_exit ((Addr a1,s1)::t1)) eqn:EX; [contradiction |].
    destruct (vClearInterruptMask_prog s1 a1) eqn:LU; [|contradiction].
    (* Enumerate only the invariant map. Expanding the state-dependent
       instruction decoder at every address prefix exhausts the memory cap. *)
    assert (PRE': true_inv (get_precondition (fun (_:store) (_:addr) => Some tt)
      (mask_clear_invs s) mask_clear_exit a1 s1 t1)).
    { unfold get_precondition. rewrite EX. exact PRE. }
    clear PRE LU EX. rename PRE' into PRE. destruct_inv 32 PRE.
    destruct PRE as [EQ PRE]. subst s1. destruct PRE as [M [C [O L]]].
    eapply NIStep with (sz:=4) (q:=mask_msr_stmt).
    + unfold effinv, effinv'. cbn [mask_clear_invs mask_clear_exit].
      rewrite mask_clear_lookup_msr by exact C. reflexivity.
    + apply mask_clear_lookup_msr, C.
    + intros c1 s1 x1 XS.
      assert (W: exec_stmt armv6mtypctx s mask_msr_stmt
        (update armv6mtypctx S_PRIMASK (Some 1)) (mask_clear_result s) None).
      { apply mask_write_exec; try assumption. eapply ECast with (ct:=CAST_LOW) (w:=32) (w':=1) (n:=s R_R0); apply EVar; reflexivity. }
      pose proof (exec_stmt_deterministic (q:=mask_msr_stmt) ltac:(repeat split) W XS) as EQ.
      inversion EQ; subst. unfold mask_clear_result. rewrite (mask_reset_update _ S_PRIMASK _ 1 eq_refl).
      apply NIHere. change (mask_clear_result s = mask_clear_result s /\
        mask_clear_postcondition s (mask_clear_result s)).
      split; [reflexivity | apply mask_clear_result_post].
Qed.
