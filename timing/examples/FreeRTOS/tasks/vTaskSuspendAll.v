Require Import RTOSDemo_NoAsserts_Clz.
Require Import RISCVTiming.
Require Import NEORV32.
Import RISCVNotations.

Module Program_vTaskSuspendAll <: ProgramInformation.
    Definition entry_addr : N := 0x80000d14.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80000d20 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo_NoAsserts_Clz.
End Program_vTaskSuspendAll.

Module RISCVTiming := RISCVTiming NEORV32Base Program_vTaskSuspendAll.
Module vTaskSuspendAllAuto := RISCVTimingAutomation RISCVTiming.
Import Program_vTaskSuspendAll vTaskSuspendAllAuto.

Definition time_of_vTaskSuspendAll (t : trace) :=
    cycle_count_of_trace t = 
        tlw + taddi + tsw + tjalr.

Definition vTaskSuspendAll_timing_invs
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000d14 => Some (cycle_count_of_trace t' = 0)
| 0x80000d20 => Some (time_of_vTaskSuspendAll t)
| _ => None end | _ => None end.

Definition lifted_vTaskSuspendAll : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Lemma fold_left_add_base_0 : forall l base,
    List.fold_left N.add l base = base + List.fold_left N.add l 0.
Proof.
    induction l; intros; simpl.
        lia.
    now rewrite IHl, <- N.add_assoc, <- (IHl a).
Qed. 

Theorem vTaskSuspendAll_timing:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_vTaskSuspendAll
    (vTaskSuspendAll_timing_invs)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. reflexivity.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    repeat step. unfold time_of_vTaskSuspendAll.
    hammer.
Qed.

