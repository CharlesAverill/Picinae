Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_xTaskGetSchedulerState <: ProgramInformation.
    Definition entry_addr : N := 0x8000198c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800019a4 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_xTaskGetSchedulerState.

Module RISCVTiming := RISCVTiming cpu Program_xTaskGetSchedulerState.
Module xTaskGetSchedulerStateAuto := RISCVTimingAutomation RISCVTiming.
Import Program_xTaskGetSchedulerState xTaskGetSchedulerStateAuto.

Definition time_of_xTaskGetSchedulerState (mem : memory) (gp : N) (t : trace) :=
    cycle_count_of_trace t =
        tlw + taddi +
        (if mem Ⓓ[gp ⊖ 1924] =? 0 then ttbeq
         else tfbeq + tlw + tsltiu + tslli 1) +
        tjalr.

Definition xTaskGetSchedulerState_timing_invs (mem : memory) (gp : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000198c => Some (s V_MEM32 = mem /\ s R_GP = gp /\ cycle_count_of_trace t' = 0)
| 0x800019a4 => Some (time_of_xTaskGetSchedulerState mem gp t)
| _ => None end | _ => None end.

Theorem xTaskGetSchedulerState_timing:
  forall s t s' x' mem gp
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (GP: s R_GP = gp),
  satisfies_all
    lifted_prog
    (xTaskGetSchedulerState_timing_invs mem gp)
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

    destruct PRE as (MEM & GP & Cycles).
    repeat step; hammer.
Qed.

End TimingProof.
