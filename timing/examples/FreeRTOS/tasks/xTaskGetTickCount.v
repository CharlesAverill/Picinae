Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_xTaskGetTickCount <: ProgramInformation.
    Definition entry_addr : N := 0x80000d24.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80000d28 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_xTaskGetTickCount.

Module RISCVTiming := RISCVTiming cpu Program_xTaskGetTickCount.
Module xTaskGetTickCountAuto := RISCVTimingAutomation RISCVTiming.
Import Program_xTaskGetTickCount xTaskGetTickCountAuto.

Definition time_of_xTaskGetTickCount (t : trace) :=
    cycle_count_of_trace t =
        tlw + tjalr.

Definition xTaskGetTickCount_timing_invs
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000d24 => Some (cycle_count_of_trace t' = 0)
| 0x80000d28 => Some (time_of_xTaskGetTickCount t)
| _ => None end | _ => None end.

Theorem xTaskGetTickCount_timing:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all
    lifted_prog
    (xTaskGetTickCount_timing_invs)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. reflexivity.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    repeat step; hammer.
Qed.

End TimingProof.
