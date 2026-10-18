Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_pvTaskIncrementMutexHeldCount <: ProgramInformation.
    Definition entry_addr : N := 0x80001cd8.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80001cec => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_pvTaskIncrementMutexHeldCount.

Module RISCVTiming := RISCVTiming cpu Program_pvTaskIncrementMutexHeldCount.
Module pvTaskIncrementMutexHeldCountAuto := RISCVTimingAutomation RISCVTiming.
Import Program_pvTaskIncrementMutexHeldCount pvTaskIncrementMutexHeldCountAuto.

Definition time_of_pvTaskIncrementMutexHeldCount (mem : memory) (gp : N) (t : trace) :=
    cycle_count_of_trace t =
        tlw +
        (if mem Ⓓ[gp ⊖ 1896] =? 0 then ttbeq
         else tfbeq + tlw + taddi + tsw) +
        tjalr.

Definition pvTaskIncrementMutexHeldCount_timing_invs (mem : memory) (gp : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80001cd8 => Some (s V_MEM32 = mem /\ s R_GP = gp /\ cycle_count_of_trace t' = 0)
| 0x80001cec => Some (time_of_pvTaskIncrementMutexHeldCount mem gp t)
| _ => None end | _ => None end.

Theorem pvTaskIncrementMutexHeldCount_timing:
  forall s t s' x' mem gp
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (GP: s R_GP = gp),
  satisfies_all
    lifted_prog
    (pvTaskIncrementMutexHeldCount_timing_invs mem gp)
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
