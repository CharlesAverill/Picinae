Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_xTaskGenericNotifyStateClear <: ProgramInformation.
    Definition entry_addr : N := 0x80002328.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002360 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_xTaskGenericNotifyStateClear.

Module RISCVTiming := RISCVTiming cpu Program_xTaskGenericNotifyStateClear.
Module xTaskGenericNotifyStateClearAuto := RISCVTimingAutomation RISCVTiming.
Import Program_xTaskGenericNotifyStateClear xTaskGenericNotifyStateClearAuto.

Definition time_of_xTaskGenericNotifyStateClear (mem : memory) (gp a0 a1 : N) (t : trace) :=
    cycle_count_of_trace t =
        (if a0 =? 0 then tfbne + tlw else ttbne) +
        tcsrrci + tadd + tlbu + tlui + taddi + tlw + taddi +
        (if mem Ⓑ[(if a0 =? 0 then mem Ⓓ[gp ⊖ 1896] else a0) ⊕ a1 ⊕ 92] =? 2
         then tfbne + tsb + taddi else ttbne) +
        (if mem Ⓓ[0x80080004] =? 0 then tfbne + tcsrrsi else ttbne) +
        tjalr.

Definition xTaskGenericNotifyStateClear_timing_invs (mem : memory) (gp a0 a1 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002328 => Some (s V_MEM32 = mem /\ s R_GP = gp /\ s R_A0 = a0 /\ s R_A1 = a1 /\ cycle_count_of_trace t' = 0)
| 0x80002360 => Some (time_of_xTaskGenericNotifyStateClear mem gp a0 a1 t)
| _ => None end | _ => None end.

Theorem xTaskGenericNotifyStateClear_timing:
  forall s t s' x' mem gp a0 a1
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (GP: s R_GP = gp)
         (A0: s R_A0 = a0)
         (A1: s R_A1 = a1),
  satisfies_all
    lifted_prog
    (xTaskGenericNotifyStateClear_timing_invs mem gp a0 a1)
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

    destruct PRE as (MEM & GP & A0 & A1 & Cycles).
    repeat step; hammer.
Qed.

End TimingProof.
