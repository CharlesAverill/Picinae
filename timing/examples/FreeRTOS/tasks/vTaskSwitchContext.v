Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

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

(* Memory separation. The function stores to xYieldPendings and to two stack
   slots (saved s0 and ra) before it performs the three loads whose values
   determine its timing: uxTopReadyPriority (which feeds clz), the ready-list
   index pointer, and the next list item *)
Definition timed_reads (gp : N) (mem : memory) : list addr :=
    [ gp ⊖ 1920;
      gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[gp ⊖ 1920]) 32) * 20;
      4 + mem Ⓓ[gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[gp ⊖ 1920]) 32) * 20] ].

Definition early_writes (gp sp : N) : list addr :=
    [ gp ⊖ 1932; sp ⊖ 8; sp ⊖ 4 ].

Definition separation (gp sp : N) (mem : memory) : Prop :=
    forall r w, In r (timed_reads gp mem) -> In w (early_writes gp sp) ->
    ~ overlap 32 r 4 w 4.

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

Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr)
    (base_sp gp : N) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
    (* vApplicationStackOverflowHook
       NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
    *)
    | 0x8000e804 => Some True
    (* vTaskSwitchContext, after loading uxSchedulerSuspended *)
    | 0x80001380 => Some (
        s V_MEM32 = base_mem /\ s R_GP = gp /\ s R_SP = base_sp /\
        s R_A4 = uxSchedulerSuspended gp base_mem /\
        cycle_count_of_trace t' = tlw)
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
         (SEP : separation gp sp mem),
  satisfies_all
    lifted_prog
    (vTaskSwitchContext_timing_invs s p sp gp mem)
    exits
  ((x',s')::t).
Proof using.
    intros. apply prove_invs.
    (* The early stores don't change the timed locations. *)
    Local Ltac sep_solve :=
        match goal with H: separation _ _ _ |- _ =>
            apply H; simpl; auto 6 end.
    Local Ltac simpl_reads :=
        repeat (multimatch goal with
        | [|- context[getmem ?w ?e ?len (setmem ?w ?e2 ?len2 ?m ?a2 ?v) ?a1]] =>
            rewrite (getmem_noverlap w e e2 len len2 m a1 a2 v) by sep_solve
        | [H: context[getmem ?w ?e ?len (setmem ?w ?e2 ?len2 ?m ?a2 ?v) ?a1] |- _] =>
            rewrite (getmem_noverlap w e e2 len len2 m a1 a2 v) in H by sep_solve
        end).
    Local Ltac step := tstep r5_step; simpl_reads.
    (* ra and s0 don't affect timing. Abstracting them keeps the symbolic
       states small on the exit paths. *)
    Ltac Picinae_riscv.ISA_RISCV.ignore_vars v ::= constr:(match v with
        R_RA | R_S0 => true
      | _ => false end).

    (* Base case *)
    simpl. rewrite ENTRY. step.
    repeat split; try reflexivity. assumption. hammer.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL SEP. rename t1 into t. rename s1 into s'.
    rename mem into base_mem.

    destruct_inv 32 PRE.

    (* 0x80001380 *)
    - destruct PRE as (MEM & GP & SP & A4 & Cycles).
      repeat step.
      (* Stack-overflow paths end at the hook's self-loop *)
      all: try exact I.
      all: unfold time_of_vTaskSwitchContext, uxSchedulerSuspended,
               next_ready_task, uxTopReadyPriority in *; hammer.
      (* The bne at 0x80001418: the stepper writes the modulus as a literal,
         so match it to the branch hypothesis by conversion. *)
      all: match goal with
           | [BC: (_ =? _) = ?b |- context[negb (?x =? ?z)]] =>
               let E := fresh "E" in
               assert (E : (x =? z) = b) by exact BC;
               rewrite E; cbn [negb]; lia
           end.

    (* 0x8000e804: the overflow hook spins forever *)
    - step. exact I.
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
