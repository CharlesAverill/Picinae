Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.
Require Import memsolve.

(* Some machinery describing the CPU *)
Variable ML : N.
Variable ML_pos : 1 <= ML.

Module vTaskSwitchContextTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x8000137c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000138c | 0x8000144c => true
        | _ => false
        end | _ => false end.
End vTaskSwitchContextTime.
Module vTaskSwitchContextAuto := TimingAutomation vTaskSwitchContextTime.
Import vTaskSwitchContextTime vTaskSwitchContextAuto.

(* These expressions pop up a lot and I don't like seeing them, so just fold them up
   - time_mem    = The time in clock cycles of a memory access
   - time_branch = The time in clock cycles of a successful/taken branch
*)
Definition time_mem : N :=
    5 + (ML - 2).
Definition time_branch : N :=
    5 + (ML - 1).

(* The doubleword in static memory (offset of gp) that determines if the scheduler
   is suspended. The scheduler should be suspended when any critical behavior
   is ongoing that could be disrupted by context switching
   - Memory allocation
   - Atomic operations
   - Modifying shared memory
   - Performance optimization
*)
Definition uxSchedulerSuspended (gp : N) (mem : addr -> N) : N :=
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
Definition pxCurrentTCB (gp : N) (mem : addr -> N) : N :=
    mem Ⓓ[gp ⊖ 1896].

(* The doubleword in static memory that records the highest priority out of all
   currently-ready tasks.
*)
Definition uxTopReadyPriority (gp : N) (mem : addr -> N) : N :=
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
Definition vTaskSwitchContext_stack_frame_size : N := 16.

(* What follows are a list of assumptions we make about the well-formedness of
   static and stack memory. For example: static and stack memory should not overlap
   (this would be a stack overflow)
*)

Definition smem_stack_regions (mem : addr -> N) (gp sp : N) : list (N * addr) := 
    [(4, gp ⊖ 1952); (4, gp ⊖ 1932); (4, gp ⊖ 1896); (4, gp ⊖ 1920);
     (4, 48 ⊕ pxCurrentTCB gp mem);
     (4, gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20);
     (4, mem Ⓓ[48 ⊕ pxCurrentTCB gp mem]);
     (4, 8 ⊕ mem Ⓓ[48 ⊕ pxCurrentTCB gp mem]);
     (4, 12 ⊕ mem Ⓓ[48 ⊕ pxCurrentTCB gp mem]);
     (4, 4 ⊕ mem Ⓓ[gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20]);
     (4, 4 ⊕ mem Ⓓ[4 ⊕ mem Ⓓ[gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20]]);
     (vTaskSwitchContext_stack_frame_size, sp ⊖ vTaskSwitchContext_stack_frame_size)].

Definition noverlaps (mem : addr -> N) (gp sp : N) :=
    create_noverlaps (smem_stack_regions mem gp sp).

Definition time_of_vTaskSwitchContext (t : trace) (gp : N) (mem : addr -> N) : Prop :=
    (* is the scheduler suspended *)
    if (uxSchedulerSuspended gp mem) =? 0 then
        cycle_count_of_trace t = (* total number of cycles equals... *)
        25 + 3 * time_branch + 17 * time_mem
            (* This branch condition isn't well-documented, need to dig into source *)
          + (if (mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ])
              =? ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20)
              then 
                22 + (clz (uxTopReadyPriority gp mem) 32) + 5 * time_mem 
              else
                19 + time_branch + (clz (uxTopReadyPriority gp mem) 32) + 3 * time_mem
              (* time_branch = 5 + (memory latency - 1), # of cycles for a successful/taken branch *)
              (* time_mem = 5 + (memory latency - 2), # of cycles for a memory retreival *)
          )
    else
        cycle_count_of_trace t = 5 + time_branch + 2 * time_mem.

(* The invariant set for the proof. These are waypoints that guide us towards 
   the postcondition. We state properties here that we want to remember for later
   in the proof (anything not in an invariant is forgotten after a branch).
   The properties that we state help us prove the postcondition. We must prove
   each invariant throughout the proof. *)
Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) 
    (base_sp gp : N) (base_mem : addr -> N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
    (* vApplicationStackOverflowHook *)
    (* NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
    *)
    | 0x8000e804 => Some True
    (* vTaskSwitchContext *)
    | 0x80001380 => Some (
        exists mem, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓbase_sp 
            /\ s R_A4 = Ⓓ(uxSchedulerSuspended gp base_mem) /\
            noverlaps mem gp base_sp /\
            uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
            mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        cycle_count_of_trace t' = time_mem)
    | 0x800013b4 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        noverlaps mem gp base_sp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 7 * time_mem + time_branch)
    | 0x800013bc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        noverlaps mem gp base_sp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 9 + 8 * time_mem + time_branch)
    | 0x800013c4 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        noverlaps mem gp base_sp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 12 + 9 * time_mem + time_branch
    )
    | 0x800013cc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        noverlaps mem gp base_sp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 15 + 10 * time_mem + time_branch
    )
    | 0x80001418 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        s R_A1 = Ⓓ(mem Ⓓ[4 + (gp ⊖ 924) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]) /\
        s R_A2 = Ⓓ(addr_pxReadyTasksLists gp ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)) /\
        s R_A5 = Ⓓ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) /\
        noverlaps mem gp base_sp /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 36 + clz (uxTopReadyPriority gp mem) 32 + 2 * time_branch + 14 * time_mem)
    | 0x8000138c | 0x8000144c => Some (time_of_vTaskSwitchContext t gp base_mem)
    | _ => None
    end
| _ => None
end.

(* Lift the code into Picinae IL *)
Definition lifted_vTaskSwitchContext : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem vTaskSwitchContext_timing:
  forall s p t s' x' gp sp mem
         (ENTRY: startof t (x',s') = (Addr entry_addr,s))
         (MDL: models rvtypctx s)
         (GP : s R_GP = Ⓓgp)
         (SP : s R_SP = Ⓓsp)
         (MEM : s V_MEM32 = Ⓜmem)
         (NOVERLAPS : noverlaps mem gp sp),
  satisfies_all 
    lifted_vTaskSwitchContext                                 (* Provide lifted code *)
    (vTaskSwitchContext_timing_invs s p sp gp mem)            (* Provide invariant set *)
    exits                                                     (* Provide exit point *)
  ((x',s')::t).
Proof using.
    (* Set up our proof environment *)
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    Local Ltac unfold_vTaskSwitchContext :=
        unfold uxSchedulerSuspended, __global_size,
        vTaskSwitchContext_stack_frame_size, uxSchedulerSuspended,
        pxCurrentTCB, uxTopReadyPriority,
        addr_pxReadyTasksLists, noverlaps, smem_stack_regions,
        msub in *; psimpl.
    Local Ltac noverlap_prepare gp sp := 
        _noverlap_prepare unfold_vTaskSwitchContext gp sp.

    (* Base case *)
    simpl. rewrite ENTRY. unfold entry_addr. step.
    eexists. repeat (split; auto).
    unfold uxSchedulerSuspended, msub. now psimpl.

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
    destruct PRE as (mem & MEM & GP & SP & A4 & NOVERLAPS
        & PreservesPriority & Preserves920 & Cycles).
    repeat step.
    handle_ex. split. {
        time noverlaps_preserved unfold_vTaskSwitchContext.
    }
        unfold_create_noverlaps unfold_vTaskSwitchContext.
        split. {
            repeat rewrite getmem_noverlap; auto using noverlap_symmetry.
            
        }
        repeat split;
            repeat rewrite getmem_noverlap; auto using noverlap_symmetry.
        noverlaps_preserved unfold_vTaskSwitchContext.
        1-10: noverlap_prepare gp sp; memsolve mem gp sp.
        1-5: noverlap_prepare gp sp; memsolve mem gp sp;
            try now eapply MEM4_PCT_NOL_STATIC;
            eauto using noverlap_symmetry.
        {
            noverlap_prepare gp sp.
            repeat rewrite <- getmem_mod_l with (a := _ + _).
            rewrite getmem_mod_l.
            replace (clz _ 32) with (clz (uxTopReadyPriority gp mem) 32) by memsolve mem gp sp.
            replace ((mem [Ⓓgp ⊖ 1932 := 0 ] [Ⓓsp ⊖ 8 := n ] [Ⓓsp ⊖ 4 := n0 ])
                Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]) with
                (mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]); cycle 1.
                memsolve mem gp sp.
            rewrite getmem_mod_l.
            replace ((mem [Ⓓgp ⊖ 1932 := 0 ] [Ⓓsp ⊖ 8 := n ] [Ⓓsp ⊖ 4 := n0 ])
                Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ]) with
                (mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ]); cycle 1.
                memsolve mem gp sp. now eapply MEM4_PCT_NOL_STATIC.
            memsolve mem gp sp.
            unfold uxTopReadyPriority. now repeat rewrite getmem_mod_l; rewrite Preserves920.
            all: rewrite <- getmem_mod_l. 
                now eapply MEM4_PCT_NOL_STATIC.
            all: apply noverlap_shrink with (sp ⊖ 16) 16;
                [psimpl; lia|auto].
        }
        hammer. find_rewrites. unfold time_mem, time_branch. lia.
    unfold time_of_vTaskSwitchContext.
        rewrite BC.
        hammer. find_rewrites. unfold time_mem, time_branch. lia.

    (* 0x800013c8 *)
    destruct PRE as (mem & MEM & GP & NOVERLAPS & MEM4_MEM4_NOL_SFRAME
        & MEM4_MEM4_NOL_STATIC & MEM4_920 & MEM4_MEM4_920 & PreservesPriority
        & Preserves920 & Suspended & Cycles). destruct_noverlaps.
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. find_rewrites. unfold time_mem, time_branch. lia.

    (* 0x800013d0 *)
    destruct PRE as (mem & MEM & GP & NOVERLAPS & MEM4_MEM4_NOL_SFRAME
        & MEM4_MEM4_NOL_STATIC & MEM4_920 & MEM4_MEM4_920 & PreservesPriority
        & Preserves920 & NotSuspended & Cycles). destruct_noverlaps.
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. find_rewrites. unfold time_mem, time_branch. lia.

    (* 0x800013d8 *)
    destruct PRE as (mem & MEM & GP & NOVERLAPS & MEM4_MEM4_NOL_SFRAME
        & MEM4_MEM4_NOL_STATIC & MEM4_920 & MEM4_MEM4_920 & PreservesPriority
        & Preserves920 & NotSuspended & Cycles). destruct_noverlaps.
    step.
        repeat step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. find_rewrites. unfold time_mem, time_branch. lia.

    (* 0x800013e0 *)
    destruct PRE as (mem & MEM & GP & NOVERLAPS & MEM4_MEM4_NOL_SFRAME
        & MEM4_MEM4_NOL_STATIC & MEM4_920 & MEM4_MEM4_920 & PreservesPriority
        & Preserves920 & NotSuspended & Cycles). destruct_noverlaps.
    repeat step.
        handle_ex.
        par: try solve [noverlap_prepare gp sp; memsolve mem gp sp].
        {
            noverlap_prepare gp sp.
            replace (clz
            ((mem [Ⓓgp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
              := mem
                 Ⓓ[ 4 +
                    mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                    ] ] ]) Ⓓ[ gp ⊖ 1920 ]) 32) with 
                (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; memsolve mem gp sp; auto).
            unfold msub. now psimpl.
        } {
            noverlap_prepare gp sp; memsolve mem gp sp.
            unfold msub. psimpl.
            now rewrite N.add_comm, N.add_assoc,
                (N.add_comm _ gp), getmem_mod_l.
        } {
            noverlap_prepare gp sp.
            replace ((mem [Ⓓgp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
            := mem
               Ⓓ[ 4 +
                  mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]
               ] ]) Ⓓ[ gp ⊖ 1920 ]) with (mem Ⓓ[ gp ⊖ 1920 ]) by
               (rewrite getmem_noverlap; auto). psimpl.
            rewrite <- getmem_mod_l with (a := _ ⊖ _ + _). eauto.
        } {
            noverlap_prepare gp sp.
            replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
            psimpl.
            rewrite <- getmem_mod_l with (a := gp ⊖ _ + _).
            eauto.
        } { 
            noverlap_prepare gp sp.
            replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
            psimpl. auto.
        }
        hammer. find_rewrites. unfold time_mem, time_branch. psimpl.
        noverlap_prepare gp sp.
        replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
        lia.

    destruct PRE as (mem & MEM & GP & A1 & A2 & A5 & NOVERLAPS
        & PreservesPriority & Preserves920 & NotSuspended & Cycles).
    destruct_noverlaps.
    repeat step.
    unfold time_of_vTaskSwitchContext.
        find_rewrites.
        hammer. rewrite <- Preserves920, <- PreservesPriority.
        find_rewrites.
        replace (4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) with
            ((gp ⊖ 920) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) in BC by
            (unfold msub; now psimpl).
        rewrite Bool.negb_true_iff, getmem_mod_l in BC.
        find_rewrites. unfold time_mem, time_branch. lia.
    unfold time_of_vTaskSwitchContext.
        find_rewrites. hammer. find_rewrites.
        rewrite <- Preserves920, <- PreservesPriority.
        replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
            in BC by (unfold msub; now psimpl).
        unfold uxTopReadyPriority in *.
        rewrite Bool.negb_false_iff, getmem_mod_l in BC.
        find_rewrites. unfold time_mem, time_branch. lia.

    now repeat step.
Qed.
