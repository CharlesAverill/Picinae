(* WIP
   This is gonna be a big undertaking - need to track a ton of conditions
   and the state gets very big very fast *)

Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_eTaskGetState <: ProgramInformation.
    Definition entry_addr : N := 0x80000958.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800009e8 | 0x800009f0 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_eTaskGetState.

Module RISCVTiming := RISCVTiming cpu Program_eTaskGetState.
Module eTaskGetStateAuto := RISCVTimingAutomation RISCVTiming.
Import Program_eTaskGetState eTaskGetStateAuto.

Definition pxCurrentTCB (gp : N) (mem : memory) : N :=
    mem Ⓓ[gp ⊖ 1896].

Definition time_of_eTaskGetState (mem : memory) (gp : N) (xTask : addr) (t : trace) :=
  cycle_count_of_trace t =
    tlw + taddi +
    if (pxCurrentTCB gp mem =? xTask) then (
      ttbeq + taddi + tjalr
    ) else (
      tfbeq + tcsrrci + tlw + tlw + tlui + tlw + tlw + tlw +
      if (mem Ⓓ[0x80080004] =? 0) then (
        ttbne + tcsrrsi
      ) else (
        ttbne
      ) +
      taddi + taddi +
      if (xTask ⊕ 40 =? gp ⊖ 984) then (
        ttbeq + tjalr
      ) else (
        tfbeq + taddi +
        if (xTask ⊕ 20 =? mem Ⓓ[gp ⊖ 1900]) then (
          ttbeq + tjalr
        ) else (
          tfbeq + if (xTask ⊕ 20 =? mem Ⓓ[gp ⊖ 1904]) then (
            ttbeq + tjalr
          ) else (
            tfbeq + taddi + if (xTask ⊕ 20 =? gp ⊖ 1024) then (
              tfbne + tlw +
              if (xTask ⊕ 20 =? 0) then (
                tfbne + tlbu + taddi +
                if (99 =? xTask ⊕ 20) then (
                    ttbeq + tjalr
                ) else (
                    tfbeq + tlbu + if (99 =? xTask ⊕ 20) then (
                        ttbeq + tjalr
                    ) else (
                        tfbeq + tlbu + if (99 =? xTask ⊕ 20) then (
                            ttbeq + tjalr
                        ) else (
                            tfbeq + taddi + tjalr
                        )
                    )
                )
              ) else (
                ttbeq + tjalr
              )
            ) else (
              ttbne + taddi + taddi +
              if (xTask ⊕ 20 =? gp ⊖ 1004) then (
                ttbeq + tjalr
              ) else (
                if (xTask ⊕ 20 =? 0) then (
                  ttbeq + tjalr
                ) else (
                  tfbeq + taddi + tjalr
                )
              )
            )
          )
        )
      )
    ).

Definition eTaskGetState_timing_invs (s : store) (base_mem : memory) (gp : N)
    (xTask : addr) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000958 => Some (s V_MEM32 = base_mem /\ s R_GP = gp /\
                        s R_A0 = xTask /\
                        cycle_count_of_trace t' = 0)
| 0x80000980 => Some (s V_MEM32 = base_mem /\ s R_GP = gp /\
                        s R_A0 = xTask /\
                        base_mem Ⓓ[ gp ⊖ 1896 ] =? xTask = false /\
                        cycle_count_of_trace t' =
                          tlw + taddi + tfbeq + tcsrrci + tlw + tlw +
                          tlui + tlw + tlw + tlw)
| 0x800009e8 | 0x800009f0 => Some (time_of_eTaskGetState base_mem gp xTask t)
| _ => None end | _ => None end.

Theorem eTaskGetState_timing:
  forall s t s' x' base_mem gp xTask
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = base_mem)
         (GP: s R_GP = gp)
         (A0: s R_A0 = xTask),
  satisfies_all 
    lifted_prog
    (eTaskGetState_timing_invs s base_mem gp xTask)
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
    step. step. step.
      step.
      unfold pxCurrentTCB. hammer.
    do 7 step.
      repeat split. assumption.
      hammer.
    
    destruct PRE as (MEM & GP & A0 & Cond1 & Cycles).
    step.
      do 3 step.
      unfold pxCurrentTCB. rewrite Cond1. hammer.
    (* The proof comes to a halt here (literally) due to step *)
Abort.
