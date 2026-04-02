Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import memsolve.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_vTaskSwitchContext <: ProgramInformation.
    Definition entry_addr : N := 0x8000137c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000138c | 0x8000144c => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vTaskSwitchContext.

Module RISCVTiming := RISCVTiming cpu Program_vTaskSwitchContext.
Module vTaskSwitchContextAuto := RISCVTimingAutomation RISCVTiming.
Import Program_vTaskSwitchContext vTaskSwitchContextAuto.

(* The doubleword in static memory (offset of gp) that determines if the scheduler
   is suspended. The scheduler should be suspended when any critical behavior
   is ongoing that could be disrupted by context switching
   - Memory allocation
   - Atomic operations
   - Modifying shared memory
   - Performance optimization
*)
Definition uxSchedulerSuspended (gp : N) (mem : memory) : N :=
    mem Ⓓ[gp ⊖ 1952].

(* The address of the doubleword in static memory that is nonzero when a task is
   ready to "yield," or signal that a context switch needs to occur (either 
   voluntarily or involuntarily)
*)
Definition addr_xYieldPendings (gp : N) : addr :=
    gp - 1932.

(* A pointer in static memory to the Current Task Control Block (TCB). The TCB
   is a data structure containing all essential information for managing a task.
*)
Definition pxCurrentTCB (gp : N) (mem : memory) : N :=
    mem Ⓓ[gp ⊖ 1896].

(* The doubleword in static memory that records the highest priority out of all
   currently-ready tasks.
*)
Definition uxTopReadyPriority (gp : N) (mem : memory) : N :=
    mem Ⓓ[gp ⊖ 1920].

(* The address in static memory of a list of linked-lists that record all currently-
   ready tasks. The index into pxReadyTasksLists indicates those tasks' priority.
*)
Definition addr_pxReadyTasksLists (gp : N) : addr :=
    gp ⊖ 924.

(* The size of static memory (at the bottom of memory) and stack memory (at the
   top)
*)
Definition __global_size : N := 2048.
Definition __stack_size : N := 16.

Definition next_ready_task gp mem :=
    (gp ⊖ 920) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20.

(* What follows are a list of assumptions we make about the well-formedness of
   static and stack memory. For example: static and stack memory should not overlap
   (this would be a stack overflow)
*)

Definition static_buffer_lengths_in_bytes (a : addr) : option N :=
    match a with
    (* uxSchedulerSuspended *)
    | 1952
    (* xYieldPendings*)
    | 1932 
    (* pxCurrentTCB *)
    | 1896 
    (* uxTopReadyPriority *)
    | 1920 => Some 4
    | _ => None
    end.

Definition noverlaps gp sp mem :=
    create_noverlaps [
        (4, gp ⊖ 1952);
        (4, gp ⊖ 1932);
        (4, gp ⊖ 1896);
        (4, gp ⊖ 1920);
        (4, 48 + pxCurrentTCB gp mem);
        (4, sp ⊖ 8);
        (4, sp ⊖ 4);
        (4, mem Ⓓ[48 + pxCurrentTCB gp mem]);
        (4, next_ready_task gp mem);
        (4, 4 + mem Ⓓ[next_ready_task gp mem]);
        (4 ,4 + mem Ⓓ[4 + mem Ⓓ[next_ready_task gp mem]]);
        (4, 8 + mem Ⓓ[48 + pxCurrentTCB gp mem]);
        (4, 12 + mem Ⓓ[48 + pxCurrentTCB gp mem])
    ].

Definition time_of_vTaskSwitchContext (t : trace) (gp : N) (mem : memory) : Prop :=
  cycle_count_of_trace t = (* total number of cycles equals... *)
    tlw +
    (* is the scheduler suspended *)
    if (uxSchedulerSuspended gp mem) =? 0 then
        ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi +
        tlw + tfbne + tlw + tfbne + tlw + tfbne + tlw + ttbeq +
        tlw + taddi + tclz (uxTopReadyPriority gp mem) + tsub + taddi + tmul +
        taddi + taddi + tadd + tlw + taddi + tadd + tlw + tsw +
        (* This branch condition isn't well-documented, need to dig into source *)
        (if (mem Ⓓ[4 + mem Ⓓ[next_ready_task gp mem]])
            =? (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ⊖ 916 ⊕ gp
            then 
                tfbne + tlw + tsw
            else
                ttbne
        ) + 
        taddi + tmul + tlw + tadd + tlw + tlw + tsw + tlw + tlw + taddi + tjalr
    else
        tfbeq + taddi + tsw + tjalr.

Definition preservation mem base_mem gp :=
    uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
    base_mem Ⓓ[4 + base_mem Ⓓ[next_ready_task gp base_mem]] =
        mem Ⓓ[4 + mem Ⓓ[next_ready_task gp mem]].

(* The invariant set for the proof. These are waypoints that guide us towards 
   the postcondition. We state properties here that we want to remember for later
   in the proof (anything not in an invariant is forgotten after a branch).
   The properties that we state help us prove the postcondition. We must prove
   each invariant throughout the proof. *)
Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) 
    (base_sp gp : N) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
    (* vApplicationStackOverflowHook *)
    (* NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
    *)
    | 0x8000e804 => Some True
    (* vTaskSwitchContext *)
    | 0x80001380 => Some (
        exists mem, s V_MEM32 = mem /\ s R_GP = gp /\ s R_SP = base_sp /\
        s R_A4 = (uxSchedulerSuspended gp base_mem) /\
        noverlaps gp base_sp mem /\
        preservation mem base_mem gp /\
        cycle_count_of_trace t' = tlw)
    | 0x800013b4 => Some (exists mem, s V_MEM32 = mem /\ 
        s R_GP = gp /\
        noverlaps gp base_sp mem /\
        preservation mem base_mem gp /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = tlw + ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi + tlw)
    | 0x800013bc => Some (exists mem, s V_MEM32 = mem /\ 
        s R_GP = gp /\
        noverlaps gp base_sp mem /\
        preservation mem base_mem gp /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = tlw + ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi + tlw + tfbne + tlw)
    | 0x800013c4 => Some (exists mem, s V_MEM32 = mem /\ 
        s R_GP = gp /\
        noverlaps gp base_sp mem /\
        preservation mem base_mem gp /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = tlw + ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi + tlw + tfbne + tlw + tfbne + tlw
    )
    | 0x800013cc => Some (exists mem, s V_MEM32 = mem /\ 
        s R_GP = gp /\
        noverlaps gp base_sp mem /\
        preservation mem base_mem gp /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = tlw + ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi + tlw + tfbne + tlw + tfbne + tlw + tfbne + tlw
    )
    | 0x80001418 => Some (exists mem, s V_MEM32 = mem /\ 
        s R_GP = gp /\
        s R_A1 = mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ] /\
        s R_A2 = gp ⊖ 924 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 /\
        s R_A5 = (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ⊖ 916 ⊕ gp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = tlw + ttbeq + taddi + tsw + tsw + tlw + tlui + tsw + tlw + taddi + tlw + tfbne + tlw + tfbne + tlw + tfbne + tlw +
            ttbeq + tlw + taddi + tclz (uxTopReadyPriority gp mem) + tsub + taddi + tmul + taddi + taddi + tadd + tlw + taddi + tadd + tlw + tsw)
    | 0x8000138c | 0x8000144c => Some (time_of_vTaskSwitchContext t gp base_mem)
    | _ => None
    end
| _ => None
end.

Theorem vTaskSwitchContext_timing:
  forall s p t s' x' gp sp mem
         (ENTRY: startof t (x',s') = (Addr entry_addr,s))
         (MDL: models rvtypctx s)
         (GP : s R_GP = gp)
         (SP : s R_SP = sp)
         (MEM : s V_MEM32 = mem)
         (NOVERLAPS : noverlaps gp sp mem),
  satisfies_all 
    lifted_prog
    (vTaskSwitchContext_timing_invs s p sp gp mem)
    exits
  ((x',s')::t).
Proof using.
    (* Set up our proof environment *)
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.
    Local Ltac unfolds :=
        try match goal with
        | [H: preservation _ _ _ |- _] =>
            destruct H as (PRES1 & PRES2)
        end;
        do 2 unfold noverlaps, uxTopReadyPriority, addr_pxReadyTasksLists,
        uxSchedulerSuspended, pxCurrentTCB, next_ready_task in *.

    (* Base case *)
    simpl. rewrite ENTRY. step.
    handle_ex. split.
        split; reflexivity.
    hammer.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'. 
    rename mem into base_mem.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* 0x800015e4 *)
    destruct PRE as (mem & MEM & GP & SP & A4 & NOV & PRES & Cycles).
    repeat step. handle_ex. split.
        noverlaps_preserved unfolds.
        split.
            split.
            unfolds; unfold_create_noverlaps;
                repeat rewrite getmem_noverlap by solve_single_noverlap.
                assumption.
            unfolds; unfold_create_noverlaps;
                repeat rewrite getmem_noverlap by solve_single_noverlap.
                assumption.
        split. assumption.
        hammer.
    hammer.

    (* 0x800013c8 *)
    destruct PRE as (mem & MEM & GP & NOV & PRES & Suspended & Cycles).
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer.

    (* 0x800013d0 *)
    destruct PRE as (mem & MEM & GP & NOV & PRES & Suspended & Cycles).
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer.

    (* 0x800013d8 *)
    destruct PRE as (mem & MEM & GP & NOV & PRES & Suspended & Cycles).
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer.

    (* 0x800013e0 *)
    destruct PRE as (mem & MEM & GP & NOV & PRES & Suspended & Cycles).
    repeat step.
        handle_ex. split.
            unfolds; unfold_create_noverlaps.
            rewrite getmem_noverlap with (a1 := gp ⊖ 1920) by solve_single_noverlap.
            psimpl. reflexivity.
        split.
            unfolds; unfold_create_noverlaps.
            repeat rewrite getmem_noverlap. reflexivity.
                solve_single_noverlap.
        split.
            unfolds; unfold_create_noverlaps;
                solve_single_noverlap.
        split.
            unfolds; unfold_create_noverlaps.
            now repeat rewrite getmem_noverlap by solve_single_noverlap.
        split.
            unfolds; unfold_create_noverlaps.
            rewrite getmem_noverlap with (a1 := gp ⊖ 1920) by solve_single_noverlap.
            psimpl. psimpl in PRES2. now rewrite PRES2.
        split. assumption.
        hammer. unfold uxTopReadyPriority.
        rewrite getmem_noverlap. lia.
        unfolds; unfold_create_noverlaps; solve_single_noverlap.

    exact I.

    destruct PRE as (mem & MEM & GP & A1 & A2 & A5 & PRES1 & PRES2 & NotSuspended & Cycles).
    repeat step.
    hammer.
        unfold next_ready_task in *. psimpl in BC. psimpl. rewrite <- PRES2.
        unfold uxTopReadyPriority in *. rewrite <- PRES1.
        apply Bool.negb_true_iff in BC. rewrite BC.
        lia.
    hammer.
        unfold next_ready_task in *. psimpl in BC. psimpl. rewrite <- PRES2.
        unfold uxTopReadyPriority in *. rewrite <- PRES1.
        apply Bool.negb_false_iff in BC. rewrite BC.
        lia.
    now repeat step.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall gp mem t,
    time_of_vTaskSwitchContext t gp mem = 
    (vTaskSwitchContextAuto.cycle_count_of_trace t = 
        (if uxSchedulerSuspended gp mem =? 0
        then
        (if
            mem Ⓓ[ 4 + mem Ⓓ[ next_ready_task gp mem ] ] =?
            (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ⊖ 916 ⊕ gp
            then
            217 + 16 * T_data_latency + 2 * T_inst_latency +
            clz (uxTopReadyPriority gp mem) 32
            else
            211 + 14 * T_data_latency + 3 * T_inst_latency +
            clz (uxTopReadyPriority gp mem) 32) +
        (6 * T_data_latency + T_inst_latency)
        else 18 + (2 * T_data_latency + T_inst_latency))).
Proof.
    intros. unfold time_of_vTaskSwitchContext.
    unfold tlw, tsw, taddi, tfbne, ttbne, ttbgeu, tfbgeu, tjal, tjalr.
    psimpl.
    unfold ttbeq, tclz, tsub, tmul, tadd, tlui, tfbeq. psimpl.
    unfold T_shift_latency, NEORV32BaseConfig.CPU_FAST_SHIFT_EN.
    unfold T_mul_latency, NEORV32BaseConfig.CPU_FAST_MUL_EN.
    psimpl.
    repeat rewrite <- N.add_assoc.
    replace (217 + _) with (217 + 16 * T_data_latency + 2 * T_inst_latency + clz (uxTopReadyPriority gp mem) 32) by lia.
    replace (211 + _) with (211 + 14 * T_data_latency + 3 * T_inst_latency + clz (uxTopReadyPriority gp mem) 32) by lia.
    replace (T_data_latency + _) with (6 * T_data_latency + T_inst_latency) by lia.
    replace (T_data_latency + _) with (2 * T_data_latency + T_inst_latency) by lia.
    repeat rewrite <- N.add_assoc. reflexivity.
Qed.
