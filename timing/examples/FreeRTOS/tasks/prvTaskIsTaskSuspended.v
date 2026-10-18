Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_prvTaskIsTaskSuspended <: ProgramInformation.
    Definition entry_addr : N := 0x80000428.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80000470 | 0x80000474 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_prvTaskIsTaskSuspended.

Module RISCVTiming := RISCVTiming cpu Program_prvTaskIsTaskSuspended.
Module prvTaskIsTaskSuspendedAuto := RISCVTimingAutomation RISCVTiming.
Import Program_prvTaskIsTaskSuspended prvTaskIsTaskSuspendedAuto.

Definition time_of_prvTaskIsTaskSuspended (mem : memory) (gp a0 : N) (t : trace) :=
    cycle_count_of_trace t =
        tlw + taddi + taddi + taddi +
        if negb (mem Ⓓ[20 + a0] =? gp ⊖ 1024) then ttbne + tjalr
        else tfbne + tlw + taddi + taddi +
        if mem Ⓓ[40 + a0] =? gp ⊖ 984 then ttbeq + tjalr
        else tfbeq +
        if negb (mem Ⓓ[40 + a0] =? 0) then ttbne + tjalr
        else tfbne + tlbu + taddi +
        if mem Ⓑ[92 + a0] =? 1 then ttbeq + tjalr
        else tfbeq + tlbu +
        if mem Ⓑ[93 + a0] =? 1 then ttbeq + tjalr
        else tfbeq + tlbu + taddi + tsltu + tjalr.

Definition prvTaskIsTaskSuspended_timing_invs (mem : memory) (gp a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000428 => Some (s V_MEM32 = mem /\ s R_GP = gp /\ s R_A0 = a0 /\ cycle_count_of_trace t' = 0)
| 0x80000470 | 0x80000474 => Some (time_of_prvTaskIsTaskSuspended mem gp a0 t)
| _ => None end | _ => None end.

Theorem prvTaskIsTaskSuspended_timing:
  forall s t s' x' mem gp a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (GP: s R_GP = gp)
         (A0: s R_A0 = a0),
  satisfies_all
    lifted_prog
    (prvTaskIsTaskSuspended_timing_invs mem gp a0)
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

    destruct PRE as (MEM & GP & A0 & Cycles).
    (* psimpl prints the branch condition's 1024 as 2^10 *)
    repeat step; try change (2^10) with 1024 in *; hammer.
Qed.

End TimingProof.
