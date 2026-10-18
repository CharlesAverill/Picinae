Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_vTaskSetTimeOutState <: ProgramInformation.
    Definition entry_addr : N := 0x80001890.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800018b8 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vTaskSetTimeOutState.

Module RISCVTiming := RISCVTiming cpu Program_vTaskSetTimeOutState.
Module vTaskSetTimeOutStateAuto := RISCVTimingAutomation RISCVTiming.
Import Program_vTaskSetTimeOutState vTaskSetTimeOutStateAuto.

Definition time_of_vTaskSetTimeOutState (mem : memory) (t : trace) :=
    cycle_count_of_trace t =
        tcsrrci + tlw + tlui + tlw + tsw + tlw + tsw + tsw +
        (if mem Ⓓ[0x80080004] =? 0 then tfbne + tcsrrsi else ttbne) +
        tjalr.

Definition vTaskSetTimeOutState_timing_invs (mem : memory)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80001890 => Some (s V_MEM32 = mem /\ cycle_count_of_trace t' = 0)
| 0x800018b8 => Some (time_of_vTaskSetTimeOutState mem t)
| _ => None end | _ => None end.

Theorem vTaskSetTimeOutState_timing:
  forall s t s' x' mem
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem),
  satisfies_all
    lifted_prog
    (vTaskSetTimeOutState_timing_invs mem)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (MEM & Cycles).
    repeat step; hammer.
Qed.

End TimingProof.
