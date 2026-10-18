Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_uxTaskPriorityGet <: ProgramInformation.
    Definition entry_addr : N := 0x800009f4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80000a14 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_uxTaskPriorityGet.

Module RISCVTiming := RISCVTiming cpu Program_uxTaskPriorityGet.
Module uxTaskPriorityGetAuto := RISCVTimingAutomation RISCVTiming.
Import Program_uxTaskPriorityGet uxTaskPriorityGetAuto.

Definition time_of_uxTaskPriorityGet (mem : memory) (a0 : N) (t : trace) :=
    cycle_count_of_trace t =
        tcsrrci + tlui + tlw +
        (if a0 =? 0 then tfbne + tlw else ttbne) +
        tlw +
        (if mem Ⓓ[0x80080004] =? 0 then tfbne + tcsrrsi else ttbne) +
        tjalr.

Definition uxTaskPriorityGet_timing_invs (mem : memory) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800009f4 => Some (s V_MEM32 = mem /\ s R_A0 = a0 /\ cycle_count_of_trace t' = 0)
| 0x80000a14 => Some (time_of_uxTaskPriorityGet mem a0 t)
| _ => None end | _ => None end.

Theorem uxTaskPriorityGet_timing:
  forall s t s' x' mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = a0),
  satisfies_all
    lifted_prog
    (uxTaskPriorityGet_timing_invs mem a0)
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

    destruct PRE as (MEM & A0 & Cycles).
    repeat step; hammer.
Qed.

End TimingProof.
