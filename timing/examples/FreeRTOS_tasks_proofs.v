Require Import lifted_RTOSDemo.
Require Import riscvTiming.
Import RISCVNotations.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (vTaskSwitchContext s a) with
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
    mem Ⓓ[2144 + gp].
    (* This should actually be the below expression. Unclear on whether lifter
       has bug, seems like it isn't treating immediate as signed
    *)
    (* mem Ⓓ[gp - 1952]. *)

Definition addr_xYieldPendings (gp : N) : N :=
    gp - 1932.

Definition pxCurrentTCB (gp : N) (mem : addr -> N) : N :=
    mem Ⓓ[2200 + gp].
    (* Same as above *)
    (* mem Ⓓ[gp - 1896]. *)

Definition uxTopReadyPriority (gp : N) (mem : addr -> N) : N :=
    mem Ⓓ[gp - 1920].

Definition addr_pxReadyTasksLists (gp : N) : N :=
    gp - 924.

(* 
(* <vTaskSwitchContext> *)
    | 0x800015e0 => 0x8601a703 (* lw a4,-1952(gp) # 80080060 <uxSchedulerSuspended>  *) time_mem
    | 0x800015e4 => 0x00070863 (* beqz a4,800015f4 <vTaskSwitchContext+0x14>  *)
        if uxSchedulerSuspended (s R_GP) mem =? 0 then time_branch else 3
    | 0x800015e8 => 0x00100713 (* li a4,1  *)                                           2
    | 0x800015ec => 0x86e1aa23 (* sw a4,-1932(gp) # 80080074 <xYieldPendings>  *)       time_mem
    | 0x800015f0 => 0x00008067 (* ret  *)                                               time_branch
    | 0x800015f4 => 0xff010113 (* add sp,sp,-16  *)                                     2
    | 0x800015f8 => 0x8601aa23 (* sw zero,-1932(gp) # 80080074 <xYieldPendings>  *)     time_mem
    | 0x800015fc => 0x01212023 (* sw s2,0(sp)  *)                                       time_mem
    | 0x80001600 => 0x8981a783 (* lw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)         time_mem
    | 0x80001604 => 0xa5a5a737 (* lui a4,0xa5a5a  *)                                    2
    | 0x80001608 => 0x00112623 (* sw ra,12(sp)  *)                                      time_mem
    | 0x8000160c => 0x0307a783 (* lw a5,48(a5)  *)                                      time_mem
    | 0x80001610 => 0x00812423 (* sw s0,8(sp)  *)                                       time_mem
    | 0x80001614 => 0x00912223 (* sw s1,4(sp)  *)                                       time_mem
    | 0x80001618 => 0x0007a603 (* lw a2,0(a5)  *)                                       time_mem
    | 0x8000161c => 0x5a570713 (* add a4,a4,1445 # a5a5a5a5 <_stack_top+0x259c48b7>  *) 2
    | 0x80001620 => 0x00e61e63 (* bne a2,a4,8000163c <vTaskSwitchContext+0x5c>  *)
        if mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]] !=? 0xa5a5a5a5 then time_branch else 3
    | 0x80001624 => 0x0047a683 (* lw a3,4(a5)  *)                                       time_mem
    | 0x80001628 => 0x00c69a63 (* bne a3,a2,8000163c <vTaskSwitchContext+0x5c>  *)
        if mem Ⓓ[4 + (48 + pxCurrentTCB gp mem)] !=? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]] then time_branch else 3
    | 0x8000162c => 0x0087a703 (* lw a4,8(a5)  *)                                       time_mem
    | 0x80001630 => 0x00d71663 (* bne a4,a3,8000163c <vTaskSwitchContext+0x5c>  *)
        if mem Ⓓ[8 + (48 + pxCurrentTCB gp mem)] !=? mem Ⓓ[4 + (48 + pxCurrentTCB gp mem)] then time_branch else 3
    | 0x80001634 => 0x00c7a783 (* lw a5,12(a5)  *)                                      time_mem
    | 0x80001638 => 0x00e78a63 (* beq a5,a4,8000164c <vTaskSwitchContext+0x6c>  *)
        if mem Ⓓ[12 + (48 + pxCurrentTCB gp mem)] !=? mem Ⓓ[8 + (48 + pxCurrentTCB gp mem)] then time_branch else 3
    | 0x8000163c => 0x8981a583 (* lw a1,-1896(gp) # 80080098 <pxCurrentTCB>  *)         time_mem
    | 0x80001640 => 0x8981a503 (* lw a0,-1896(gp) # 80080098 <pxCurrentTCB>  *)         time_mem
    | 0x80001644 => 0x03458593 (* add a1,a1,52  *)                                      2
    | 0x80001648 => 0x429100ef (* jal 80012270 <vApplicationStackOverflowHook>  *)      time_branch + timeof(vApplicationStackOverflowHook)
    | 0x8000164c => 0x8801a503 (* lw a0,-1920(gp) # 80080080 <uxTopReadyPriority>  *)   time_mem
    | 0x80001650 => 0x01f00493 (* li s1,31  *)                                          2
    | 0x80001654 => 0x02c120ef (* jal 80013680 <__clzsi2>  *)                           time_branch + timeof(__clzsi2)
    | 0x80001658 => 0x40a484b3 (* sub s1,s1,a0  *)                                      2
    | 0x8000165c => 0x01400713 (* li a4,20  *)                                          2
    | 0x80001660 => 0x02e48733 (* mul a4,s1,a4  *)                                      2
    | 0x80001664 => 0xc6418793 (* add a5,gp,-924 # 80080464 <pxReadyTasksLists>  *)     2
    | 0x80001668 => 0xc6418413 (* add s0,gp,-924 # 80080464 <pxReadyTasksLists>  *)     2
    | 0x8000166c => 0x00e787b3 (* add a5,a5,a4  *)                                      2
    | 0x80001670 => 0x0007a783 (* lw a5,0(a5)  *)                                       time_mem
    | 0x80001674 => 0x00079c63 (* bnez a5,8000168c <vTaskSwitchContext+0xac>  *)
        if mem Ⓓ[(GP - 924) + ((31 - mem Ⓓ[GP - 1920]) * 20)] !=? 0 then time_branch else 3
    | 0x80001678 => 0x000015b7 (* lui a1,0x1  *)                                        2
    | 0x8000167c => 0x80014537 (* lui a0,0x80014  *)                                    2
    | 0x80001680 => 0x41358593 (* add a1,a1,1043 # 1413 <__stack_size+0x12b5>  *)       2
    | 0x80001684 => 0xbd050513 (* add a0,a0,-1072 # 80013bd0 <_etext>  *)               2
    | 0x80001688 => 0x409100ef (* jal 80012290 <vAssertCalled>  *)                      time_branch + timeof(vAssertCalled)
    | 0x8000168c => 0x01400793 (* li a5,20  *)                                          2
    | 0x80001690 => 0x02f487b3 (* mul a5,s1,a5  *)                                      2
    | 0x80001694 => 0x00f40733 (* add a4,s0,a5  *)                                      2
    | 0x80001698 => 0x00472683 (* lw a3,4(a4)  *)                                       time_mem
    | 0x8000169c => 0x00878793 (* add a5,a5,8  *)                                       2
    | 0x800016a0 => 0x00f407b3 (* add a5,s0,a5  *)                                      2
    | 0x800016a4 => 0x0046a683 (* lw a3,4(a3)  *)                                       time_mem
    | 0x800016a8 => 0x00d72223 (* sw a3,4(a4)  *)                                       time_mem
    | 0x800016ac => 0x00f69663 (* bne a3,a5,800016b8 <vTaskSwitchContext+0xd8>  *)
        if mem Ⓓ[4 + mem Ⓓ[4 + (addr_pxReadyTasksLists + ((31 - uxTopReadyPriority) * 20))]] !=? 
            (addr_pxReadyTasksLists + (((31 - uxTopReadyPriority) * 20) + 8)) then time_branch else 3
    | 0x800016b0 => 0x00c72783 (* lw a5,12(a4)  *)                                      time_mem
    | 0x800016b4 => 0x00f72223 (* sw a5,4(a4)  *)                                       time_mem
    | 0x800016b8 => 0x01400793 (* li a5,20  *)                                          2
    | 0x800016bc => 0x02f484b3 (* mul s1,s1,a5  *)                                      2
    | 0x800016c0 => 0x00c12083 (* lw ra,12(sp)  *)                                      time_mem
    | 0x800016c4 => 0x00940433 (* add s0,s0,s1  *)                                      2
    | 0x800016c8 => 0x00442783 (* lw a5,4(s0)  *)                                       time_mem
    | 0x800016cc => 0x00812403 (* lw s0,8(sp)  *)                                       time_mem
    | 0x800016d0 => 0x00412483 (* lw s1,4(sp)  *)                                       time_mem
    | 0x800016d4 => 0x00c7a783 (* lw a5,12(a5)  *)                                      time_mem
    | 0x800016d8 => 0x88f1ac23 (* sw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)         time_mem
    | 0x800016dc => 0x8981a783 (* lw a5,-1896(gp) # 80080098 <pxCurrentTCB>  *)         time_mem
    | 0x800016e0 => 0x00012903 (* lw s2,0(sp)  *)                                       time_mem
    | 0x800016e4 => 0x01010113 (* add sp,sp,16  *)                                      2
    | 0x800016e8 => 0x00008067 (* ret  *)                                               5 + (ML - 1)
*)

Definition vTaskSwitchContext_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x800015f0 | 0x800016e8 => true
  | _ => false
  end | _ => false end.

Definition timing_postcondition (t : trace) (gp : N) (mem : addr -> N) : Prop :=
    cycle_count_of_trace t = if (uxSchedulerSuspended gp mem) =? 0 then 77 else 5 + time_branch + 2 * time_mem.

Notation "x !=? y" := (negb (x =? y)) (at level 70, no associativity) : N_scope.

Definition gp_sp_noverlap (gp sp : N) : Prop :=
    ~overlap 32 gp __global_size sp vTaskSwitchContext_stack_frame_size.

Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) (base_sp : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0x800015e4 => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓbase_sp /\ s R_A4 = Ⓓ(uxSchedulerSuspended gp mem) /\ gp_sp_noverlap gp base_sp /\
        cycle_count_of_trace t' = time_mem)
    (* The proof expressions get big, so throw in a few intermediate invariants to constrain the goal space's size *)
    (* | 0x80001610 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16)  /\ gp_sp_noverlap gp base_sp /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A4 = Ⓓ(0xa5a5a) /\
        cycle_count_of_trace t' = 4 + 6 * time_mem + time_branch
    ) *)
    | 0x80001620 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ((0xa5a5a << 12) + 1445) /\
        cycle_count_of_trace t' = 6 + 9 * time_mem + time_branch)
    | 0x8000163c => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        cycle_count_of_trace t' = 6 + 9 * time_mem + time_branch + 
            if mem Ⓓ[mem Ⓓ[ 48 + pxCurrentTCB gp mem ]] !=? 0xa5a5a5a5 then time_branch else 3
    )
    | 0x80001648 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ cycle_count_of_trace t' = 8 + 11 * time_mem + 2 * time_branch)
    | 0x80001628 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ 
        cycle_count_of_trace t' = 
            if (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5) then 
                (9 + 10 * time_mem + time_branch)
            else
                ((if mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] !=? 0xa5a5a5a5 then time_branch else 3) + 
                    (6 + 10 * time_mem + time_branch)))
    | 0x80001630 | 0x80001638 
        | 0x80001654 | 0x80001674 | 0x80001688 | 0x800016ac => Some (cycle_count_of_trace t' = 99)
    | 0x800015f0 | 0x800016e8 => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
            timing_postcondition t gp mem)
    | _ => None end
| _ => None
end.

Definition lifted_vTaskSwitchContext : program :=
    (* lift_via_list vTaskSwitchContext start_vTaskSwitchContext end_vTaskSwitchContext. *)
    lift_riscv vTaskSwitchContext.

Compute lifted_vTaskSwitchContext empty_store start_vTaskSwitchContext.

Theorem vTaskSwitchContext_welltyped: welltyped_prog rvtypctx lifted_vTaskSwitchContext.
(* Proof. Picinae_typecheck. Qed. *)
Admitted.

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
    exists mem, gp. repeat split; assumption.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try eassumption; [idtac|apply vTaskSwitchContext_welltyped].
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* 0x800015e4 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A4 [GP_SP_FAR Cycles]]]]]]].
    step. step. step. step. step. step. step. step. step. step. step. step.
    do 2 eexists. repeat split. unfold msub. now psimpl.
        unfold pxCurrentTCB. admit. admit.
    hammer. rewrite A4, BC, Cycles. lia.

    (* 0x800015e8 *)
    step. step. handle_ex.
    unfold timing_postcondition. unfold uxSchedulerSuspended. psimpl. 
    hammer. fold (uxSchedulerSuspended gp mem). rewrite A4, BC, Cycles. lia.
    
    (* 0x80001620 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A5 [A2 [A4 Cycles]]]]]]]].
    step. handle_ex.
        hammer. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        rewrite A2, A4, Cycles. lia.
    step. handle_ex.
        hammer. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        rewrite A2, A4, Cycles, BC. lia.

    (* 0x80001620 *)
    destruct PRE as [mem [gp [MEM [GP Cycles]]]].
    step.
        handle_ex. hammer. rewrite Hsv, A2, Cycles.

    (* 0x80001624 *)
    step. hammer. rewrite Hsv0, Hsv, BC, PRE. lia.

    (* 0x80001628 *)
    step. step. step. step. hammer. rewrite Hsv0, Hsv, BC, PRE. psimpl.

    step. step. step. step. step. step. step. step. step. step. step. step.
        hammer. rewrite Hsv, BC.
        rewrite PRE. lia.
    step. step. step. step. step. step. step. step.
        hammer. rewrite Hsv, BC.
        rewrite PRE. lia.

    (* 0x2ddc *)
    step.
    step. step. step. step. step. step. step. step. step.
        (* Infinite loop *) admit.
    step. step. step. step. hammer. rewrite Hsv, Hsv0, BC, PRE. lia.

    (* 0x2df0 *)
    step. step. step. step. step. step. step. step. step. step.
        (* Infinite loop *) admit.
    step. step. step. step.
        hammer. rewrite Hsv, Hsv0, BC, PRE. lia.

    (* 0x2e04 *)
    step. step. step. step. step. step. step. step. step. step.
        (* Infinite loop *) admit.
    step. step. step. step.
        hammer. rewrite Hsv, Hsv0, BC, PRE. lia.

    (* 0x2e18 *)
    step. step. step. step. step.
        (* Infinite loop *) admit.
    step. step. step. step. step. step. step. step. step.
        (* Infinite loop *) admit.

    (* 0x2e90 *)
    step. step. step. step. step. step. step. step. step. step. step. step. step. step.
        step. step. step. step. step.
        hammer. rewrite Hsv, BC, PRE. lia.
    step. step. step. step. step.
        (* Infinite loop *) admit.
    
    (* 0x2ef4 *)
    step. step. step. step. step. step. step. step. step. step. step. step.
        hammer. rewrite Hsv, Hsv0, BC, PRE. psimpl. 
