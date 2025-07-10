Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module vTaskSuspendAllTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x80000d14.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x80000d20 => true
    | _ => false
  end | _ => false end.
End vTaskSuspendAllTime.

Module vTaskSuspendAllAuto := TimingAutomation vTaskSuspendAllTime.
Import vTaskSuspendAllTime vTaskSuspendAllAuto.

Definition time_of_vTaskSuspendAll (t : trace) :=
    cycle_count_of_trace t = 2 + time_branch + 2 * time_mem.

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

