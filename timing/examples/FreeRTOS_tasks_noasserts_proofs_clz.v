Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import memsolve.

(* Some machinery describing the CPU *)
Variable ML : N.
Variable ML_pos : 1 <= ML.
Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.
End riscv_toa.
Module riscvT := MakeTimingContents riscvTiming riscv_toa.
Export riscvT.
Definition cycle_count_of_trace := cycle_count_of_trace time_of_addr.

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

(* The goal with the below functions is to use for function timing invariants, e.g.
        cycle_count_of_trace t' = 
            func_time + cycle_count_of_trace (subtrace_before_address t' func_entry_addr))
    This would be nice because then you don't have to worry about annoying arithmetic.
    
    Unfortunately, it seems like you'd need to put an invariant like the following
    at the JAL instruction leading into the function:
        cycle_count_of_trace (subtrace_before_address t' func_entry_addr)) = 
            cycle_count_of_trace t (* where t is the whole program trace *)
    And I'm not sure if the definition of subtrace_before_address allows for this
    to be proven and therefore utilized.

    This is because the definition recurses over the list looking for the provided
    address, but if the address hasn't been hit yet it will traverse over some 
    unknown subtail of the list and therefore we can't simplify it and get an answer.
    Or, what if the function has been visited? We don't want to segment based on THAT
    entry to the function.

    Will have to revisit later, definitely need something like this for scaling up.
*)

Fixpoint subtrace_since_address (t : trace) (a : addr) : trace :=
    match t with
    | (Addr a', st) :: tl => if (a =? a') then (Addr a', st) :: nil else
        (Addr a', st) :: subtrace_since_address tl a
    | _ => nil
    end.

Fixpoint subtrace_before_address (t : trace) (a : addr) : trace :=
    match t with
    | (Addr a', st) :: tl => if (a =? a') then tl else
        subtrace_before_address tl a
    | _ => nil
    end.

Definition time_before_address (t : trace) (a : addr) : N :=
    cycle_count_of_trace (subtrace_before_address t a).

(* The size of static memory (at the bottom of memory) and stack memory (at the
   top)
*)
Definition __global_size : N := 2048.
Definition vTaskSwitchContext_stack_frame_size : N := 16.

(* What follows are a list of assumptions we make about the well-formedness of
   static and stack memory. For example: static and stack memory should not overlap
   (this would be a stack overflow)
*)
Definition gp_sp_noverlap (gp sp : N) : Prop :=
    ~overlap 32 (gp ⊖ __global_size) __global_size (sp ⊖ vTaskSwitchContext_stack_frame_size) vTaskSwitchContext_stack_frame_size.

(* These two definitions state that any two of the above buffers we're interested
   in do not overlap
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

Definition smem_well_formed (gp : N) : Prop :=
    forall x y len_x len_y,
                x <> y ->
                static_buffer_lengths_in_bytes x = Some len_x ->
                static_buffer_lengths_in_bytes y = Some len_y ->
            ~ overlap 32
                (gp ⊖ x) len_x
                (gp ⊖ y) len_y.

(* I don't yet know the significance of the address
      gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20
   but it appears very frequently and it must not overlap with things like the
   TCB or stack memory. Some of these assumptions can actually be proven due to 
   the boundaries of clz (count leading zeroes) being 0..32
*)
Definition pxCurrentTCB_noverlap_clz_static (gp : N) (mem : addr -> N) : Prop :=
    ~ overlap 32
        (48 + pxCurrentTCB gp mem) 4
        (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4.

Definition clz_noverlap_smem (gp : N) mem : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (gp ⊖ x) len_x
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4.

(* The TCB doesn't overlap static memory or the stack frame *)
Definition pxCurrentTCB_noverlap_static (gp : N) (mem : addr -> N) : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (48 + pxCurrentTCB gp mem) 4
            (gp ⊖ x) len_x.

Definition pxCurrentTCB_noverlap_stackframe (gp base_sp : N) (mem : addr -> N) : Prop :=
    ~ overlap 32
        (48 + pxCurrentTCB gp mem) 4
        (base_sp ⊖ 16) 16.

(* The address contained in the current TCB doesn't overlap with static memory
   or the stack frame *)
Definition mem_pxCurrentTCB_noverlap_stackframe (gp base_sp : N) (mem : addr -> N) : Prop :=
    ~ overlap 32
        (mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
        (base_sp ⊖ 16) 16.

Definition mem_pxCurrentTCB_noverlap_static (gp : N) (mem : addr -> N) : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
            (gp ⊖ x) len_x.

(* Offsets into the address contained in the current TCB don't overlap with 
   the clz address or stack memory *)
Definition offset_mem_pxCurrentTCB_noverlap_clz (gp : N) (mem : addr -> N) : Prop :=
    forall k, k = 8 \/ k = 12 ->
        ~ overlap 32
            (k + mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4.

Definition clz_noverlap_sframe (gp base_sp : N) (mem : addr -> N) : Prop :=
    ~ overlap 32 
        (base_sp ⊖ 16) 16
        (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4.

(* An offset into the buffer at the clz address doesn't overlap with static
   memory or the stack frame *)
Definition mem4_pxCurrentTCB_noverlap_stackframe (gp base_sp : N) (mem : addr -> N) : Prop :=
        ~ overlap 32
        (base_sp ⊖ 16) 16
            (4 + mem Ⓓ[gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20]) 4.

Definition mem4_pxCurrentTCB_noverlap_static (gp : N) (mem : addr -> N) : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (gp ⊖ x) 4
            (4 + mem Ⓓ[gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20]) 4.

(* An offset into the buffer at an offset into the buffer at the clz address 
   doesn't overlap with static memory or the stack frame *)
Definition mem4_mem4_noverlap_stackframe (gp base_sp : N) (mem : addr -> N) :=
    ~ overlap 32
        (base_sp ⊖ 16) 16
        (4 + mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ]) 4.

Definition mem4_mem4_noverlap_static (gp : N) (mem : addr -> N) :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (gp ⊖ x) 4
            (4 + mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ]) 4.

(* Stick them all together *)
Definition common_noverlaps gp base_sp mem : Prop :=
    gp_sp_noverlap gp base_sp /\
    smem_well_formed gp /\
    pxCurrentTCB_noverlap_static gp mem /\
    pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
    pxCurrentTCB_noverlap_clz_static gp mem /\
    clz_noverlap_smem gp mem /\
    mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
    mem_pxCurrentTCB_noverlap_static gp mem /\
    offset_mem_pxCurrentTCB_noverlap_clz gp mem /\
    clz_noverlap_sframe gp base_sp mem /\
    mem4_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
    mem4_pxCurrentTCB_noverlap_static gp mem.

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
            common_noverlaps gp base_sp mem /\
            mem4_mem4_noverlap_stackframe gp base_sp mem /\
            mem4_mem4_noverlap_static gp mem /\
            ~ overlap 32
                (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
                (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
            ~ overlap 32
                (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
                (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4 /\
            uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
            mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        cycle_count_of_trace t' = time_mem)
    | 0x800013b4 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        common_noverlaps gp base_sp mem /\
        mem4_mem4_noverlap_stackframe gp base_sp mem /\
        mem4_mem4_noverlap_static gp mem /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4 /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 7 * time_mem + time_branch)
    | 0x800013bc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        common_noverlaps gp base_sp mem /\
        mem4_mem4_noverlap_stackframe gp base_sp mem /\
        mem4_mem4_noverlap_static gp mem /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4 /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 9 + 8 * time_mem + time_branch)
    | 0x800013c4 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        common_noverlaps gp base_sp mem /\
        mem4_mem4_noverlap_stackframe gp base_sp mem /\
        mem4_mem4_noverlap_static gp mem /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4 /\
        uxTopReadyPriority gp mem = uxTopReadyPriority gp base_mem /\
        mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ] =
            base_mem Ⓓ[ 4 + base_mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (uxTopReadyPriority gp base_mem) 32) * 20 ] ]  /\
        (uxSchedulerSuspended gp base_mem =? 0) = true /\
        cycle_count_of_trace t' = 12 + 9 * time_mem + time_branch
    )
    | 0x800013cc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\
        common_noverlaps gp base_sp mem /\
        mem4_mem4_noverlap_stackframe gp base_sp mem /\
        mem4_mem4_noverlap_static gp mem /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
        ~ overlap 32
            (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
            (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4 /\
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
        common_noverlaps gp base_sp mem /\
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

(* The exit points for vTaskSwitchContext *)
Definition vTaskSwitchContext_exit (t:trace) : bool :=
  match t with (Addr a,_)::_ => match a with
  | 0x8000138c | 0x8000144c => true
  | _ => false
  end | _ => false end.

(* Lift the code into Picinae IL *)
Definition lifted_vTaskSwitchContext : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* Let's build some automation machinery to streamline the proof *)
Ltac unfold_decompose :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section]; cbn [N.land].
Tactic Notation "unfold_decompose" "in" hyp(H) :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section] in H; cbn [N.land] in H.
Ltac unfold_time_of_addr :=
    cbv [time_of_addr neorv32_cycles_upper_bound]; cbn - [setmem getmem].
Tactic Notation "unfold_time_of_addr" "in" hyp(H) :=
    cbv [time_of_addr neorv32_cycles_upper_bound] in H; cbn - [setmem getmem].
Ltac unfold_cycle_count_list :=
    unfold cycle_count_of_trace; repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single; fold cycle_count_of_trace.
Ltac fold_times :=
    fold time_mem; fold time_branch.
Ltac hammer :=
    unfold_cycle_count_list; unfold_time_of_addr; unfold_decompose; fold_times; psimpl; try lia.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

(* The entrypoint to vTaskSwitchContext *)
Definition start_vTaskSwitchContext : N := 0x8000137c.

Theorem vTaskSwitchContext_timing:
  forall s p t s' x' gp sp mem
         (ENTRY: startof t (x',s') = (Addr start_vTaskSwitchContext,s))
         (MDL: models rvtypctx s)
         (GP : s R_GP = Ⓓgp)
         (SP : s R_SP = Ⓓsp)
         (MEM : s V_MEM32 = Ⓜmem)
         (NOVERLAPS : common_noverlaps gp sp mem)
         (MEM4_NOVERLAPS : 
            mem4_mem4_noverlap_stackframe gp sp mem /\
            mem4_mem4_noverlap_static gp mem /\
            ~ overlap 32
                (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
                (4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ] ) 4 /\
            ~ overlap 32
                (gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) 4
                (mem Ⓓ[4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20 ]]) 4)
         ,
  satisfies_all 
    lifted_vTaskSwitchContext                                 (* Provide lifted code *)
    (vTaskSwitchContext_timing_invs s p sp gp mem)            (* Provide invariant set *)
    vTaskSwitchContext_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof using.
    (* Set up our proof environment *)
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.
    Local Ltac handle_ex := eexists; eexists; repeat split; try eassumption.
    Local Ltac noverlap_prepare gp sp :=
        _noverlap_prepare
            uxSchedulerSuspended pxCurrentTCB __global_size
             vTaskSwitchContext_stack_frame_size uxSchedulerSuspended 
             gp_sp_noverlap smem_well_formed pxCurrentTCB_noverlap_static
             pxCurrentTCB_noverlap_stackframe pxCurrentTCB_noverlap_clz_static
             clz_noverlap_smem mem_pxCurrentTCB_noverlap_stackframe 
             mem_pxCurrentTCB_noverlap_static offset_mem_pxCurrentTCB_noverlap_clz
             clz_noverlap_sframe mem4_pxCurrentTCB_noverlap_stackframe
             mem4_pxCurrentTCB_noverlap_static uxTopReadyPriority mem4_mem4_noverlap_static
             mem4_mem4_noverlap_stackframe addr_pxReadyTasksLists
            gp sp.
    Local Ltac destruct_noverlaps :=
        match goal with
        | [H: common_noverlaps _ _ _ |- _] =>
            destruct H as [GP_SP_FAR [SMEM_WELL_FORMED [PCT_NOL_STATIC 
            [PCT_NOL_SFRAME [PCT_NOL_CLZ [CLZ_NOL_STATIC 
            [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC [OFF_MEM_PCT_NOL_CLZ
            [CLZ_NOL_SFRAME [MEM4_PCT_NOL_SFRAME MEM4_PCT_NOL_STATIC]]]]]]]]]]]
        end. 
    destruct_noverlaps.

    (* Base case *)
    simpl. rewrite ENTRY. step.
    exists mem. destruct MEM4_NOVERLAPS, H0, H1. repeat split; try assumption.
    unfold uxSchedulerSuspended. unfold msub. psimpl. reflexivity.

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
    destruct PRE as [mem [MEM [GP [SP [A4 [NOVERLAPS [MEM4_MEM4_NOL_SFRAME
        [MEM4_MEM4_NOL_STATIC [MEM4_920 [MEM4_MEM4_920 [PreservesPriority 
        [Preserves920 Cycles]]]]]]]]]]]].
        destruct_noverlaps.
    step. step. step. step. step. step. step. step. step. step.
    handle_ex.
        1-10: noverlap_prepare gp sp; memsolve mem gp sp. 
        {
            unfold mem4_mem4_noverlap_stackframe.
            noverlap_prepare gp sp; memsolve mem gp sp; eauto using noverlap_symmetry.
            now eapply MEM4_PCT_NOL_STATIC.
        } {
            unfold mem4_mem4_noverlap_static. intros.
            noverlap_prepare gp sp; memsolve mem gp sp; eauto using noverlap_symmetry.
            now eapply MEM4_PCT_NOL_STATIC.
        } {
            noverlap_prepare gp sp; memsolve mem gp sp; eauto using noverlap_symmetry.
        } {
            noverlap_prepare gp sp; memsolve mem gp sp; eauto using noverlap_symmetry.
            now eapply MEM4_PCT_NOL_STATIC.
        } {
            noverlap_prepare gp sp; memsolve mem gp sp; auto.
        } {
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
        hammer. rewrite A4, BC, Cycles. lia.
    step. step.
        unfold time_of_vTaskSwitchContext.
        rewrite BC.
        hammer. rewrite A4, BC, Cycles. lia.

    (* 0x800013c8 *)
    destruct PRE as [mem [MEM [GP [NOVERLAPS [MEM4_MEM4_NOL_SFRAME
        [MEM4_MEM4_NOL_STATIC [MEM4_920 [MEM4_MEM4_920 [PreservesPriority 
        [Preserves920 [Suspended Cycles]]]]]]]]]]]. destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. rewrite Hsv, Hsv0, BC, Cycles. lia.

    (* 0x800013d0 *)
    destruct PRE as [mem [MEM [GP [NOVERLAPS [MEM4_MEM4_NOL_SFRAME
        [MEM4_MEM4_NOL_STATIC [MEM4_920 [MEM4_MEM4_920 [PreservesPriority [Preserves920 
        [NotSuspended Cycles]]]]]]]]]]].
    destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. rewrite Hsv, Hsv0, Cycles, BC. lia.

    (* 0x800013d8 *)
    destruct PRE as [mem [MEM [GP [NOVERLAPS [MEM4_MEM4_NOL_SFRAME
        [MEM4_MEM4_NOL_STATIC [MEM4_920 [MEM4_MEM4_920 [PreservesPriority [Preserves920 
        [NotSuspended Cycles]]]]]]]]]]]. destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step.
        handle_ex.
        hammer. rewrite Hsv, Hsv0, BC, Cycles. lia.

    (* 0x800013e0 *)
    destruct PRE as [mem [MEM [GP [NOVERLAPS [MEM4_MEM4_NOL_SFRAME 
        [MEM4_MEM4_NOL_STATIC [MEM4_920 [MEM4_MEM4_920 [PreservesPriority 
        [Preserves920 [NotSuspended Cycles]]]]]]]]]]]. destruct_noverlaps.
    step. step. step. step. step. step. step. step. step. step. step.
    step. step. step. step.
        handle_ex.
            1-15: try solve [noverlap_prepare gp sp; memsolve mem gp sp].
        {
            unfold uxTopReadyPriority.
            noverlap_prepare gp sp.
            replace (clz
            ((mem [Ⓓgp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
              := mem
                 Ⓓ[ 4 +
                    mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                    ] ] ]) Ⓓ[ gp ⊖ 1920 ]) 32) with 
                (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; memsolve mem gp sp; auto).
            unfold msub at 4. now psimpl.
        } {
            noverlap_prepare gp sp; memsolve mem gp sp. unfold addr_pxReadyTasksLists.
            unfold msub; psimpl; simpl (2^32 - _ mod _).
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
            rewrite <- getmem_mod_l with (a := _ ⊖ _ + _). 
            eapply MEM4_MEM4_NOL_SFRAME.
        } {
            noverlap_prepare gp sp.
            replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
            psimpl.
            rewrite <- getmem_mod_l with (a := gp ⊖ _ + _).
            eapply MEM4_MEM4_NOL_STATIC; eassumption.
        } { 
            noverlap_prepare gp sp.
            replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
            psimpl.
            now rewrite Preserves920.
        }
        hammer. rewrite Hsv, Hsv0, BC, Cycles. psimpl.
        noverlap_prepare gp sp.
        replace (clz ((mem [Ⓓ_ := _ ]) Ⓓ[ gp ⊖ 1920 ]) 32) 
                with (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) by
                (f_equal; rewrite getmem_noverlap; auto).
        lia.
    (* Inside vApplicationStackOverflowHook *)
    step. step. step. step. step. step. step. step. step. step. exact I.

    destruct PRE as [mem [MEM [GP [A1 [A2 [A5 [NOVERLAPS
        [PreservesPriority [Preserves920 [NotSuspended Cycles]]]]]]]]]].
    destruct_noverlaps.
    step. step. step. step. step. step. step. step. step. step. step.
    unfold time_of_vTaskSwitchContext.
    rewrite getmem_mod_l with (m := base_mem) (a := gp ⊖ _ + _).
    rewrite <- Preserves920, <- PreservesPriority.
    apply Bool.negb_true_iff in BC.
    replace (4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) with
        ((gp ⊖ 920) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) in BC by
        (unfold msub; now psimpl).
    rewrite getmem_mod_l in BC. rewrite BC, NotSuspended.
    hammer. rewrite A1, A5.
    replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
        by (unfold msub; now psimpl).
    unfold uxTopReadyPriority in *.
    rewrite getmem_mod_l, BC, Cycles.
    cbn [negb]. psimpl. lia.

    step. step. step. step. step. step. step. step. step. step. step. step.
    unfold time_of_vTaskSwitchContext.
    apply Bool.negb_false_iff in BC.
    replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
        in BC by (unfold msub; now psimpl).
    unfold uxTopReadyPriority in *.
    rewrite <- getmem_mod_l with (m := base_mem) (a := gp ⊖ _ + _) in Preserves920.
    rewrite getmem_mod_l in BC.
    rewrite <- Preserves920, <- PreservesPriority, BC, NotSuspended.
    hammer. rewrite A1, A5.
    replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
        by (unfold msub; now psimpl).
    unfold uxTopReadyPriority in *. rewrite getmem_mod_l, BC, Cycles.
    cbn [negb]. psimpl. lia.

    step. exact I.
Qed.
