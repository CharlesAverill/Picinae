Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_ulTaskGenericNotifyValueClear <: ProgramInformation.
    Definition entry_addr : N := 0x80002364.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002398 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_ulTaskGenericNotifyValueClear.

Module RISCVTiming := RISCVTiming cpu Program_ulTaskGenericNotifyValueClear.
Module ulTaskGenericNotifyValueClearAuto := RISCVTimingAutomation RISCVTiming.
Import Program_ulTaskGenericNotifyValueClear ulTaskGenericNotifyValueClearAuto.

Definition time_of_ulTaskGenericNotifyValueClear (mem : memory) (a0 : N) (t : trace) :=
    cycle_count_of_trace t =
        (if a0 =? 0 then tfbne + tlw else ttbne) +
        tcsrrci + tlui + tslli 2 + tlw + tadd + tlw + tlw + tandn + tsw +
        (if mem Ⓓ[0x80080004] =? 0 then tfbne + tcsrrsi else ttbne) +
        tjalr.

Definition ulTaskGenericNotifyValueClear_timing_invs (mem : memory) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002364 => Some (s V_MEM32 = mem /\ s R_A0 = a0 /\ cycle_count_of_trace t' = 0)
| 0x80002398 => Some (time_of_ulTaskGenericNotifyValueClear mem a0 t)
| _ => None end | _ => None end.

Theorem ulTaskGenericNotifyValueClear_timing:
  forall s t s' x' mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = a0),
  satisfies_all
    lifted_prog
    (ulTaskGenericNotifyValueClear_timing_invs mem a0)
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
