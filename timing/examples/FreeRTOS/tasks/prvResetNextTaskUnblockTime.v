Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_prvResetNextTaskUnblockTime <: ProgramInformation.
    Definition entry_addr : N := 0x80000478.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000048c => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_prvResetNextTaskUnblockTime.

Module RISCVTiming := RISCVTiming cpu Program_prvResetNextTaskUnblockTime.
Module prvResetNextTaskUnblockTimeAuto := RISCVTimingAutomation RISCVTiming.
Import Program_prvResetNextTaskUnblockTime prvResetNextTaskUnblockTimeAuto.

Definition time_of_prvResetNextTaskUnblockTime (mem : addr -> N) (gp : N) (t : trace) :=
    cycle_count_of_trace t =
        tlw + tlw +
        (if mem Ⓓ[mem Ⓓ[gp ⊖ 1900]] =? 0 then 
            tfbne + taddi
         else
            ttbne + tlw + tlw + tlw + tjal) +
        tsw + tjalr.

Definition prvResetNextTaskUnblockTime_timing_invs (s : store) (base_mem : addr -> N) (gp : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000478 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_GP = Ⓓgp /\ cycle_count_of_trace t' = 0)
| 0x8000048c => Some (time_of_prvResetNextTaskUnblockTime base_mem gp t)
| _ => None end | _ => None end.

Theorem prvResetNextTaskUnblockTime_timing:
  forall s t s' x' base_mem gp
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (GP: s R_GP = Ⓓgp),
  satisfies_all 
    lifted_prog
    (prvResetNextTaskUnblockTime_timing_invs s base_mem gp)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (MEM & GP & Cycles).
    repeat step; fold_big_subs.
    unfold time_of_prvResetNextTaskUnblockTime.
        hammer.
    unfold time_of_prvResetNextTaskUnblockTime.
        hammer.
Qed.

End TimingProof.
