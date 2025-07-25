Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_vTaskSuspendAll <: ProgramInformation.
    Definition entry_addr : N := 0x80000d14.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80000d20 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vTaskSuspendAll.

Module RISCVTiming := RISCVTiming cpu Program_vTaskSuspendAll.
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

Theorem vTaskSuspendAll_timing:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_prog
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

End TimingProof.
