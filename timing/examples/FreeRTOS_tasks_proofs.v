Require Import lifted_RTOSDemo.
Require Import riscvTiming.
Import RISCVNotations.

Definition vTaskSwitchContext (a : addr) : N :=
    match a with
    (* <vApplicationStackOverflowHook> *)
    | 0x80012270 => 0x80014537 (* lui a0,0x80014  *)
    | 0x80012274 => 0xff010113 (* add sp,sp,-16  *)
    | 0x80012278 => 0x46050513 (* add a0,a0,1120 # 80014460 <_etext+0x890>  *)
    | 0x8001227c => 0x00112623 (* sw ra,12(sp)  *)
    (* WARNING/TODO/NOTICE : 
        I'm manually replacing the instruction here at 0x80012280:
            0x20d000ef (* jal 80012c8c <printf> *)
        with a nop:
            0x00000013 (* addi zero, zero, 0 *)
        This is because dealing with printf is a huge pain for my timing proof,
        and this goes into an infinite loop (by design)anyways just a few 
        instructions later! So replacing this call has no bearing on a timing
        proof (although it may have a bearing on future correctness proofs)

        This is a lot easier than recompiling the operating system :)
    *)
    (* | 0x80012280 => 0x20d000ef (* jal 80012c8c <printf>  *) *)
    | 0x80012280 => 0x00000013 (* addi zero, zero, 0 *)
    (* TODO 
       switch this back to
            0x30047073 (* csrc mstatus,8  *)
       I don't want to implement the ZICSR extension rn
    *)
    (* | 0x80012284 => 0x30047073 (* csrc mstatus,8  *) *)
    | 0x80012284 => 0x00000013 (* addi zero, zero, 0 *)
    | 0x80012288 => 0x0000006f (* j 80012288 <vApplicationStackOverflowHook+0x18>  *)
    (* <vAssertCalled> *)
    | 0x80012290 => 0x00050613 (* mv a2,a0  *)
    | 0x80012294 => 0x80014537 (* lui a0,0x80014  *)
    | 0x80012298 => 0xfe010113 (* add sp,sp,-32  *)
    | 0x8001229c => 0x47c50513 (* add a0,a0,1148 # 8001447c <_etext+0x8ac>  *)
    | 0x800122a0 => 0x00112e23 (* sw ra,28(sp)  *)
    | 0x800122a4 => 0x00012623 (* sw zero,12(sp)  *)
    (* WARNING/TODO/NOTICE : 
        I'm manually replacing the instruction here at 0x80012280:
            0x20d000ef (* jal 80012c8c <printf> *)
        with a nop:
            0x00000013 (* addi zero, zero, 0 *)
        This is because dealing with printf is a huge pain for my timing proof,
        and this goes into an infinite loop (by design)anyways just a few 
        instructions later! So replacing this call has no bearing on a timing
        proof (although it may have a bearing on future correctness proofs)

        This is a lot easier than recompiling the operating system :)
    *)
    (* | 0x800122a8 => 0x1e5000ef (* jal 80012c8c <printf>  *) *)
    | 0x800122a8 => 0x00000013 (* addi zero, zero, 0 *)
    (* TODO 
       switch this back to
            0x30047073 (* csrc mstatus,8  *)
       I don't want to implement the ZICSR extension rn
    *)
    (* | 0x800122ac => 0x30047073 (* csrc mstatus,8  *) *)
    | 0x800122ac => 0x00000013 (* addi zero, zero, 0 *)
    | 0x800122b0 => 0x80080737 (* lui a4,0x80080  *)
    | 0x800122b4 => 0x00472783 (* lw a5,4(a4) # 80080004 <xCriticalNesting>  *)
    | 0x800122b8 => 0x00178793 (* add a5,a5,1  *)
    | 0x800122bc => 0x00f72223 (* sw a5,4(a4)  *)
    | 0x800122c0 => 0x00c12783 (* lw a5,12(sp)  *)
    | 0x800122c4 => 0x02078263 (* beqz a5,800122e8 <vAssertCalled+0x58>  *)
    | 0x800122c8 => 0x00472783 (* lw a5,4(a4)  *)
    | 0x800122cc => 0xfff78793 (* add a5,a5,-1  *)
    | 0x800122d0 => 0x00f72223 (* sw a5,4(a4)  *)
    | 0x800122d4 => 0x00079463 (* bnez a5,800122dc <vAssertCalled+0x4c>  *)
    (* TODO 
       switch this back to
            0x30047073 (* csrc mstatus,8  *)
       I don't want to implement the ZICSR extension rn
    *)
    (* | 0x800122d8 => 0x30046073 (* csrs mstatus,8  *) *)
    | 0x800122d8 => 0x00000013 (* addi zero, zero, 0*)
    | 0x800122dc => 0x01c12083 (* lw ra,28(sp)  *)
    | 0x800122e0 => 0x02010113 (* add sp,sp,32  *)
    | 0x800122e4 => 0x00008067 (* ret  *)
    | 0x800122e8 => 0x00000013 (* nop  *)
    | 0x800122ec => 0x00000013 (* nop  *)
    | 0x800122f0 => 0xfd1ff06f (* j 800122c0 <vAssertCalled+0x30>  *)
    (* <__clzsi2> *)
    | 0x80013680 => 0x000107b7 (* lui a5,0x10  *)
    | 0x80013684 => 0x02f57a63 (* bgeu a0,a5,800136b8 <__clzsi2+0x38>  *)
    | 0x80013688 => 0x10053793 (* sltiu a5,a0,256  *)
    | 0x8001368c => 0x0017b793 (* seqz a5,a5  *)
    | 0x80013690 => 0x00379793 (* sll a5,a5,0x3  *)
    | 0x80013694 => 0x80015737 (* lui a4,0x80015  *)
    | 0x80013698 => 0x02000693 (* li a3,32  *)
    | 0x8001369c => 0x40f686b3 (* sub a3,a3,a5  *)
    | 0x800136a0 => 0x00f55533 (* srl a0,a0,a5  *)
    | 0x800136a4 => 0xc5c70793 (* add a5,a4,-932 # 80014c5c <__clz_tab>  *)
    | 0x800136a8 => 0x00a787b3 (* add a5,a5,a0  *)
    | 0x800136ac => 0x0007c503 (* lbu a0,0(a5) # 10000 <__stack_size+0xfea2>  *)
    | 0x800136b0 => 0x40a68533 (* sub a0,a3,a0  *)
    | 0x800136b4 => 0x00008067 (* ret  *)
    | 0x800136b8 => 0x01000737 (* lui a4,0x1000  *)
    | 0x800136bc => 0x01800793 (* li a5,24  *)
    | 0x800136c0 => 0xfce57ae3 (* bgeu a0,a4,80013694 <__clzsi2+0x14>  *)
    | 0x800136c4 => 0x01000793 (* li a5,16  *)
    | 0x800136c8 => 0xfcdff06f (* j 80013694 <__clzsi2+0x14>  *)
    (* <vTsakSwitchContext> *)
    | 0x800015e0 => 0x8601a703 (* lw a4,-1952(gp) # 80080060 <uxSchedulerSuspended>  *)
    | 0x800015e4 => 0x00070863 (* beqz a4,800015f4 <vTaskSwitchContext+0x14>  *)
    | 0x800015e8 => 0x00100713 (* li a4,1  *)
    | 0x800015ec => 0x86e1aa23 (* sw a4,-1932(gp) # 80080074 <xYieldPendings>  *)
    | 0x800015f0 => 0x00008067 (* ret  *)
    | 0x800015f4 => 0xff010113 (* add sp,sp,-16  *)
    | 0x800015f8 => 0x8601aa23 (* sw zero,-1932(gp) # 80080074 <xYieldPendings>  *)
    | 0x800015fc => 0x01212023 (* sw s2,0(sp)  *)
    | 0x80001600 => 0x8981a783 (* lw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)
    | 0x80001604 => 0xa5a5a737 (* lui a4,0xa5a5a  *)
    | 0x80001608 => 0x00112623 (* sw ra,12(sp)  *)
    | 0x8000160c => 0x0307a783 (* lw a5,48(a5)  *)
    | 0x80001610 => 0x00812423 (* sw s0,8(sp)  *)
    | 0x80001614 => 0x00912223 (* sw s1,4(sp)  *)
    | 0x80001618 => 0x0007a603 (* lw a2,0(a5)  *)
    | 0x8000161c => 0x5a570713 (* add a4,a4,1445 # a5a5a5a5 <_stack_top+0x259c48b7>  *)
    | 0x80001620 => 0x00e61e63 (* bne a2,a4,8000163c <vTaskSwitchContext+0x5c>  *)
    | 0x80001624 => 0x0047a683 (* lw a3,4(a5)  *)
    | 0x80001628 => 0x00c69a63 (* bne a3,a2,8000163c <vTaskSwitchContext+0x5c>  *)
    | 0x8000162c => 0x0087a703 (* lw a4,8(a5)  *)
    | 0x80001630 => 0x00d71663 (* bne a4,a3,8000163c <vTaskSwitchContext+0x5c>  *)
    | 0x80001634 => 0x00c7a783 (* lw a5,12(a5)  *)
    | 0x80001638 => 0x00e78a63 (* beq a5,a4,8000164c <vTaskSwitchContext+0x6c>  *)
    | 0x8000163c => 0x8981a583 (* lw a1,-1896(gp) # 80080098 <pxCurrentTCB>  *)
    | 0x80001640 => 0x8981a503 (* lw a0,-1896(gp) # 80080098 <pxCurrentTCB>  *)
    | 0x80001644 => 0x03458593 (* add a1,a1,52  *)
    | 0x80001648 => 0x429100ef (* jal 80012270 <vApplicationStackOverflowHook>  *)
    | 0x8000164c => 0x8801a503 (* lw a0,-1920(gp) # 80080080 <uxTopReadyPriority>  *)
    | 0x80001650 => 0x01f00493 (* li s1,31  *)
    | 0x80001654 => 0x02c120ef (* jal 80013680 <__clzsi2>  *)
    | 0x80001658 => 0x40a484b3 (* sub s1,s1,a0  *)
    | 0x8000165c => 0x01400713 (* li a4,20  *)
    | 0x80001660 => 0x02e48733 (* mul a4,s1,a4  *)
    | 0x80001664 => 0xc6418793 (* add a5,gp,-924 # 80080464 <pxReadyTasksLists>  *)
    | 0x80001668 => 0xc6418413 (* add s0,gp,-924 # 80080464 <pxReadyTasksLists>  *)
    | 0x8000166c => 0x00e787b3 (* add a5,a5,a4  *)
    | 0x80001670 => 0x0007a783 (* lw a5,0(a5)  *)
    | 0x80001674 => 0x00079c63 (* bnez a5,8000168c <vTaskSwitchContext+0xac>  *)
    | 0x80001678 => 0x000015b7 (* lui a1,0x1  *)
    | 0x8000167c => 0x80014537 (* lui a0,0x80014  *)
    | 0x80001680 => 0x41358593 (* add a1,a1,1043 # 1413 <__stack_size+0x12b5>  *)
    | 0x80001684 => 0xbd050513 (* add a0,a0,-1072 # 80013bd0 <_etext>  *)
    | 0x80001688 => 0x409100ef (* jal 80012290 <vAssertCalled>  *)
    | 0x8000168c => 0x01400793 (* li a5,20  *)
    | 0x80001690 => 0x02f487b3 (* mul a5,s1,a5  *)
    | 0x80001694 => 0x00f40733 (* add a4,s0,a5  *)
    | 0x80001698 => 0x00472683 (* lw a3,4(a4)  *)
    | 0x8000169c => 0x00878793 (* add a5,a5,8  *)
    | 0x800016a0 => 0x00f407b3 (* add a5,s0,a5  *)
    | 0x800016a4 => 0x0046a683 (* lw a3,4(a3)  *)
    | 0x800016a8 => 0x00d72223 (* sw a3,4(a4)  *)
    | 0x800016ac => 0x00f69663 (* bne a3,a5,800016b8 <vTaskSwitchContext+0xd8>  *)
    | 0x800016b0 => 0x00c72783 (* lw a5,12(a4)  *)
    | 0x800016b4 => 0x00f72223 (* sw a5,4(a4)  *)
    | 0x800016b8 => 0x01400793 (* li a5,20  *)
    | 0x800016bc => 0x02f484b3 (* mul s1,s1,a5  *)
    | 0x800016c0 => 0x00c12083 (* lw ra,12(sp)  *)
    | 0x800016c4 => 0x00940433 (* add s0,s0,s1  *)
    | 0x800016c8 => 0x00442783 (* lw a5,4(s0)  *)
    | 0x800016cc => 0x00812403 (* lw s0,8(sp)  *)
    | 0x800016d0 => 0x00412483 (* lw s1,4(sp)  *)
    | 0x800016d4 => 0x00c7a783 (* lw a5,12(a5)  *)
    | 0x800016d8 => 0x88f1ac23 (* sw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)
    | 0x800016dc => 0x8981a783 (* lw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)
    | 0x800016e0 => 0x00012903 (* lw s2,0(sp)  *)
    | 0x800016e4 => 0x01010113 (* add sp,sp,16  *)
    | 0x800016e8 => 0x00008067 (* ret  *)
    | _ => 0
    end.

Definition start_vTaskSwitchContext : N := 0x800015e0.
Definition end_vTaskSwitchContext : N := 0x800016e8.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (vTaskSwitchContext a) with
        | Some x => x | _ => 0 end.
End riscv_toa.

Module riscvT := MakeTimingContents riscvTiming riscv_toa.
Export riscvT.

Definition cycle_count_of_trace := cycle_count_of_trace time_of_addr.

Definition time_mem : N :=
    5 + (ML - 2).

Definition time_branch : N :=
    5 + (ML - 1).

Definition uxSchedulerSuspended (gp : N) (mem : addr -> N) : N :=
    (* mem Ⓓ[2144 + gp]. *)
    (* This should actually be the below expression. Unclear on whether lifter
       has bug, seems like it isn't treating immediate as signed
    *)
    mem Ⓓ[gp ⊖ 1952].

Definition addr_xYieldPendings (gp : N) : N :=
    gp - 1932.

Definition pxCurrentTCB (gp : N) (mem : addr -> N) : N :=
    (* mem Ⓓ[2200 + gp]. *)
    (* Same as above *)
    mem Ⓓ[gp ⊖ 1896].

Definition uxTopReadyPriority (gp : N) (mem : addr -> N) : N :=
    mem Ⓓ[gp ⊖ 1920].

Definition addr_pxReadyTasksLists (gp : N) : N :=
    gp - 924.

Definition vTaskSwitchContext_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x800015f0 | 0x800016e8 => true
  | _ => false
  end | _ => false end.

Notation "x !=? y" := (negb (x =? y)) (at level 70, no associativity) : N_scope.

Definition timing_postcondition (t : trace) (s : store) (gp : N) (mem : addr -> N) : Prop :=
    if (uxSchedulerSuspended gp mem) !=? 0 then 
        cycle_count_of_trace t = 5 + time_branch + 2 * time_mem
    else
        cycle_count_of_trace t = 47 + 5 * time_branch + 25 * time_mem.

Definition gp_sp_noverlap (gp sp : N) : Prop :=
    ~overlap 32 gp __global_size (sp - vTaskSwitchContext_stack_frame_size) vTaskSwitchContext_stack_frame_size.

(* Axiom printf_time : N. *)
Axiom __clzsi2_time : N.
Axiom vAssertCalled_time : N.
Axiom vApplicationStackOverflowHook_time : N.

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

(* The goal with the above function is to use for function timing invariants, e.g.
        cycle_count_of_trace t' = 
            func_time + cycle_count_of_trace (subtrace_before_address t' func_entry_addr))
    This would be nice because then you don't have to worry about annoying arithmetic.
    
    Unfortunately, it seems like you'd need to put an invariant like the following
    at the JAL instruction leading into the function:
        cycle_count_of_trace (subtrace_before_address t' func_entry_addr)) = 
            cycle_count_of_trace t (* where t is the whole program trace *)
    And I'm not sure if the definition of subtrace_before_address allows for this
    to be proven and therefore utilized.

    Will have to revisit later, definitely need something like this for scaling up.
*)

Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) (base_sp : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    (* vAssertCalled *)
    | 0x800122e4 => Some (cycle_count_of_trace t' = 
        vAssertCalled_time + (
            40 + 3 * time_branch + 14 * time_mem            
        ))
    (* vApplicationStackOverflowHook *)
    (* NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
       Hamlen says control flow should never go here?
    *)
    | 0x80012288 => Some True
    (* __clzsi2 *)
    (* | 0x800136b4 => Some (cycle_count_of_trace t' =
        __clzsi2_time + 
            ()) *)
    (* __clzsi2 correctness spec *)
    (* | 0x80001658 => Some (exists mem gp,
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A0 = (* bitwidth *) Ⓓ(32 - (N.log2 (uxTopReadyPriority gp mem)))
    ) *)
    | 0x800015e4 => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓbase_sp 
            /\ s R_A4 = Ⓓ(uxSchedulerSuspended gp mem) /\ gp_sp_noverlap gp base_sp /\
        cycle_count_of_trace t' = time_mem)
    | 0x80001620 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ((0xa5a5a << 12) + 1445) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 9 * time_mem + time_branch)
    (* | 0x80001624 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? 0xa5a5a5a5 = false) *)
    | 0x80001628 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5) = false /\
        cycle_count_of_trace t' = 
            (* if (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5) then 
                (9 + 10 * time_mem + time_branch)
            else *)
                (9 + 10 * time_mem + time_branch))
    | 0x80001630 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5) = false /\
        (mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) = false /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 12 + 11 * time_mem + time_branch
    )
    | 0x80001638 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5) = false /\
        (mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) = false /\
        (mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) = false /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 15 + 12 * time_mem + time_branch
    )
    (* | 0x8000163c => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 9 * time_mem + time_branch + 
            (if mem Ⓓ[mem Ⓓ[ 48 + pxCurrentTCB gp mem ]] !=? 0xa5a5a5a5 then time_branch else
                3 + 
                (if mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]] then 
                    time_branch + time_mem else 3 +
                    (if mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] then 
                        time_branch + 2 * time_mem else 3 + 3 + 3 * time_mem)))
    ) *)
     (* | 0x80001648 => Some True *)
    (* | 0x80001648 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ 
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 8 + 11 * time_mem + time_branch + 
            (if mem Ⓓ[mem Ⓓ[ 48 + pxCurrentTCB gp mem ]] !=? 0xa5a5a5a5 then time_branch else
                3 + 
                (if mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]] then 
                    time_branch + time_mem else 3 +
                    (if mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] then 
                        time_branch + 2 * time_mem else 3 + 3 + 3 * time_mem)))) *)
    | 0x80001654 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_S1 = Ⓓ31 /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 17 + 2 * time_branch + 13 * time_mem)
    | 0x80001674 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_S0 = Ⓓ(gp ⊖ 924) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 29 + 2 * time_branch + 14 * time_mem)
    | 0x80001688 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 40 + 2 * time_branch + 14 * time_mem
    )
    | 0x800016ac => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 39 + 3 * time_branch + 17 * time_mem
    )
    | 0x800015f0 | 0x800016e8 => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
            timing_postcondition t s gp mem)
    | _ => None end
| _ => None
end.

Definition lifted_vTaskSwitchContext : program :=
    lift_riscv vTaskSwitchContext.

Ltac unfold_decompose :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section]; simpl (_ .& _).
Tactic Notation "unfold_decompose" "in" hyp(H) :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section] in H; simpl (_ .& _) in H.

Ltac unfold_time_of_addr :=
    cbv [time_of_addr neorv32_cycles_upper_bound]; cbn - [getmem].
Tactic Notation "unfold_time_of_addr" "in" hyp(H) :=
    cbv [time_of_addr neorv32_cycles_upper_bound] in H; cbn - [getmem] in H.

Ltac unfold_cycle_count_list :=
    unfold cycle_count_of_trace; repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single; fold cycle_count_of_trace.

Ltac fold_times :=
    fold time_mem; fold time_branch.

Ltac hammer :=
    unfold_cycle_count_list; unfold_time_of_addr; unfold_decompose; fold_times; psimpl; try lia.

Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Lemma noverlap_index:
  forall w a1 len1 a2 len2 index size
  (NO : ~ overlap w a1 len1 a2 len2)
  (IN : index + size <= len1),
  ~ overlap w (a1 + index) size a2 len2.
Proof.
  intros.
  remember (a1 + index) as a1'. apply noverlap_shrink with (a1:=a1) (len1:=len1).
  rewrite Heqa1'. rewrite add_msub_l.
  apply N.le_trans with (m:=index+size). rewrite <-N.add_le_mono_r. apply N.Div0.mod_le.
  assumption.
  assumption.
Qed.

Lemma getmem_nbyte_distance:
  forall w e m a1 a2 n v,
  msub w a1 a2 > n ->
  msub w a2 a1 > n ->
    getmem w e n (setmem w e n m a2 v) a1 = getmem w e n m a1.
Proof.
  intros.
  apply getmem_noverlap.
  clear - H H0.
  apply sep_noverlap; try (left; lia || right; lia).
Qed.

Theorem vTaskSwitchContext_timing:
  forall s p t s' x' gp sp
         (ENTRY: startof t (x',s') = (Addr start_vTaskSwitchContext,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (GP : s R_GP = Ⓓgp)
         (SP : s R_SP = Ⓓsp)
         (GP_SP_FAR : gp_sp_noverlap gp sp),
  satisfies_all 
    lifted_vTaskSwitchContext                                 (* Provide lifted code *)
    (vTaskSwitchContext_timing_invs s p sp)                  (* Provide invariant set *)
    vTaskSwitchContext_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.
    Local Ltac handle_ex := eexists; eexists; repeat split; try eassumption.
    Local Ltac destruct_pre PRE := destruct PRE as [mem [gp [MEM [GP [GP_SP_FAR Cycles]]]]].

    (* Base case *)
    simpl. rewrite ENTRY. step. rename m into mem.
    exists mem, gp. repeat split; try assumption.
    unfold uxSchedulerSuspended. unfold msub. psimpl. reflexivity. 

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* 0x800015e4 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A4 [GP_SP_FAR Cycles]]]]]]].
    step. step. step. step. step. step. step. step. step. step. step. step.
    do 2 eexists. repeat split. unfold msub. now psimpl.
        (* rewrite getmem_noverlap; cycle 1.
            apply noverlap_shrink with (a1 := gp) (len1 := __global_size); cycle 1.
            unfold gp_sp_noverlap in GP_SP_FAR.
            apply noverlap_symmetry, 
                noverlap_shrink with (a1 := (sp - vTaskSwitchContext_stack_frame_size)) (len1 := vTaskSwitchContext_stack_frame_size).
            psimpl.  *)
        admit. admit.
        unfold uxSchedulerSuspended. repeat rewrite getmem_noverlap.
            apply BC.
        1-5: try now (apply sep_noverlap; left; unfold msub; psimpl; lia).
        1-4: apply noverlap_shrink with (a1 := gp) (len1 := __global_size); psimpl.
        admit. (* Overlapping stuff *)
        hammer. rewrite A4, BC, Cycles. lia.
    step. step. handle_ex.
        unfold timing_postcondition. unfold uxSchedulerSuspended in *.
            rewrite getmem_frame; cycle 1.
                left. psimpl. lia.
                left. psimpl. lia.
        rewrite BC. cbn [negb].
        hammer. rewrite A4, BC, Cycles. lia.
    
    (* 0x80001620 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A5 [A2 [A4 [BR0 Cycles]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        hammer. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        rewrite A2, A4, BC, Cycles. lia.

    (* 0x80001628 *)
    destruct PRE as [mem [gp [MEM [GP [A2 [A3 [A5 [NotSuspended [Br Cycles]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex. hammer. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *. 
        rewrite A2, A3, Cycles, BC. lia.

    (* 0x80001630 *)
    destruct PRE as [mem [gp [MEM [GP [A3 [A4 [A5 [B1 [B2 [NotSuspended Cycles]]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step.
        handle_ex. hammer. rewrite A3, A4, BC, Cycles. lia.

    (* 0x80001638 *)
    destruct PRE as [mem [gp [MEM [GP [A3 [A4 [A5 [B1 [B2 [B3 [NotSuspended Cycles]]]]]]]]]]].
    step. step. step.
        handle_ex. hammer. rewrite A4, A5, BC, Cycles. lia.
    step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)

    (* 0x80001654 *)
    destruct PRE as [mem [gp [MEM [GP [S1 [A3 [A4 [A5 [NotSuspended Cycles]]]]]]]]].
    admit. (* Internals of __clzsi2 *)

    (* 0x80001674 *)
    destruct PRE as [mem [gp [MEM [GP [S0 [A3 [A4 [A5 [NotSuspended Cycles]]]]]]]]].
    step. step. step. step. step. step. step. step. step.
    handle_ex.
        admit. (* NotSuspended overwrite goal *)
    hammer. rewrite A5, BC, Cycles. lia.

    (* 0x80001678 *)
    step. step. step. step. 
        handle_ex. hammer. rewrite A5, BC, Cycles. lia.

    (* 0x80001688 *)
    destruct PRE as [mem [gp [MEM [GP [A3 [A4 [A5 [NotSuspended Cycles]]]]]]]].
    step. (* Now in vAssertCalled *)
        admit. (* TODO : add two invariants for the branches here *)

    (* 0x800016ac *)
    destruct PRE as [mem [gp [MEM [GP [NotSuspended Cycles]]]]].
    step. step. step. step. step. step. step. step. step.
        step. step. step. step.
    handle_ex. unfold timing_postcondition.
    replace (uxSchedulerSuspended gp _ !=? 0) with false.
    hammer. rewrite Hsv, Hsv0, BC, Cycles. lia. 

    unfold "!=?". admit. (* NotSuspended overlap goal *)

    (* 0x800016b0 *)
    step. step. step. step. step. step. step. step. step.
        step. step. step. step. step.
    handle_ex. unfold timing_postcondition.
    replace (uxSchedulerSuspended gp _ !=? 0) with false.
    hammer. rewrite Hsv, Hsv0, BC, Cycles.
    (* Need to add another set of conditions to the postcondition for this exit
       point. Probably depends on output of __clzsi2. Where is its return value
       stored? It seems like s1 but that don't make no sense
    *) admit. admit. (* NotSuspended overlap goal *)

    step. exact I. (* Infinite loop case *)

    admit. (* Once I prove the postcondition for vAssertCalled,
              this case should go away *)
Admitted.

