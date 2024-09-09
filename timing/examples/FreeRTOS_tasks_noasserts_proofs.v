Require Import RTOSDemo_NoAsserts.
Require Import riscvTiming.
Import RISCVNotations.

Definition start_vTaskSwitchContext : N := 0x80001390.
Definition end_vTaskSwitchContext : N := 0x80001460.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts a) with
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
    (* mem â¹[2144 + gp]. *)
    (* This should actually be the below expression. Unclear on whether lifter
       has bug, seems like it isn't treating immediate as signed
    *)
    mem â¹[gp â 1952].

Definition addr_xYieldPendings (gp : N) : N :=
    gp - 1932.

Definition pxCurrentTCB (gp : N) (mem : addr -> N) : N :=
    (* mem â¹[2200 + gp]. *)
    (* Same as above *)
    mem â¹[gp â 1896].

Definition uxTopReadyPriority (gp : N) (mem : addr -> N) : N :=
    mem â¹[gp â 1920].

Definition addr_pxReadyTasksLists (gp : N) : N :=
    gp - 924.

Definition vTaskSwitchContext_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x800013a0 | 0x80001460 => true
  | _ => false
  end | _ => false end.

Definition timing_postcondition (t : trace) (s : store) (gp : N) (mem : addr -> N) a2 a5 : Prop :=
    if (uxSchedulerSuspended gp mem) =? 0 then
        cycle_count_of_trace t = 25 + 3 * time_branch + 17 * time_mem + (
            if a2 =? a5 then 3 + 2 * time_mem else time_branch)
    else
        cycle_count_of_trace t = 5 + time_branch + 2 * time_mem.

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

Definition time_before_address (t : trace) (a : addr) :=
    cycle_count_of_trace (subtrace_before_address t a).

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

    This is because the definition recurses over the list looking for the provided
    address, but if the address hasn't been hit yet it will traverse over some 
    unknown subtail of the list and therefore we can't simplify it and get an answer.
    Or, what if the function has been visited? We don't want to segment based on THAT
    entry to the function.

    Will have to revisit later, definitely need something like this for scaling up.
*)

Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) (base_sp : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    (* vApplicationStackOverflowHook *)
    (* NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
       Hamlen says control flow should never go here?
    *)
    | 0x8000e8ec => Some True
    (* __clzsi2 *)
    (* | 0x800136b4 => Some (cycle_count_of_trace t' =
        __clzsi2_time + 
            ()) *)
    (* __clzsi2 correctness spec *)
    (* | 0x80001658 => Some (exists mem gp,
        s R_A2 = â¹(mem â¹[mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = â¹(mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = â¹(mem â¹[48 + pxCurrentTCB gp mem]) /\
        s R_A0 = (* bitwidth *) â¹(32 - (N.log2 (uxTopReadyPriority gp mem)))
    ) *)
    | 0x80001394 => Some (
        exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\ s R_SP = â¹base_sp 
            /\ s R_A4 = â¹(uxSchedulerSuspended gp mem) /\ gp_sp_noverlap gp base_sp /\
        cycle_count_of_trace t' = time_mem)
    | 0x800013c8 => Some (exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\ s R_SP = â¹(base_sp â 16) /\
        s R_A5 = â¹(mem â¹[48 + pxCurrentTCB gp mem]) /\
        s R_A2 = â¹(mem â¹[mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = â¹((0xa5a5a << 12) + 1445) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 7 * time_mem + time_branch)
    | 0x800013d0 => Some (exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\
        s R_A2 = â¹(mem â¹[mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = â¹(mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = â¹(mem â¹[48 + pxCurrentTCB gp mem]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        (mem â¹[ mem â¹[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        cycle_count_of_trace t' = 9 + 8 * time_mem + time_branch)
    | 0x800013d8 => Some (exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\
        s R_A3 = â¹(mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = â¹(mem â¹[8 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = â¹(mem â¹[48 + pxCurrentTCB gp mem]) /\
        (mem â¹[ mem â¹[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        (mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]] =? mem â¹[mem â¹[48 + pxCurrentTCB gp mem]]) = true /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 12 + 9 * time_mem + time_branch
    )
    | 0x800013e0 => Some (exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\
        s R_A3 = â¹(mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = â¹(mem â¹[8 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = â¹(mem â¹[12 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        (mem â¹[ mem â¹[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        (mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]] =? mem â¹[mem â¹[48 + pxCurrentTCB gp mem]]) = true /\
        (mem â¹[8 + mem â¹[48 + pxCurrentTCB gp mem]] =? mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) = true /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 15 + 10 * time_mem + time_branch
    )
    | 0x8000142c => Some (exists mem gp, s V_MEM32 = âmem /\ s R_GP = â¹gp /\
        s R_A2 = â¹(4 + mem â¹[4 + (mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]])]) /\
        s R_A3 = â¹(mem â¹[4 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = â¹(mem â¹[8 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = â¹(mem â¹[12 + mem â¹[48 + pxCurrentTCB gp mem]]) /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 17 + 2 * time_branch + 11 * time_mem)
    | 0x800013a0 | 0x80001460 => Some (
        exists mem gp a2 a5, s V_MEM32 = âmem /\ s R_GP = â¹gp /\
            timing_postcondition t s gp mem a2 a5)
    | _ => None end
| _ => None
end.

Definition lifted_vTaskSwitchContext : program :=
    lift_riscv RTOSDemo_NoAsserts.

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
         (GP : s R_GP = â¹gp)
         (SP : s R_SP = â¹sp)
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
    step. step. step. step. step. step. step. step. step. step.
    do 2 eexists. repeat split. unfold msub. now psimpl.
        admit. admit.
        (* unfold uxSchedulerSuspended. repeat rewrite getmem_noverlap.
            apply BC.
        1-5: try now (apply sep_noverlap; left; unfold msub; psimpl; lia).
        1-4: apply noverlap_shrink with (a1 := gp) (len1 := __global_size); psimpl. *)
        admit. (* Overlapping stuff *)
        hammer. rewrite A4, BC, Cycles. psimpl. lia.
    step. step. handle_ex. handle_ex.
        unfold timing_postcondition. unfold uxSchedulerSuspended in *.
            rewrite getmem_frame; cycle 1.
                left. psimpl. lia.
                left. psimpl. lia.
        rewrite BC.
        hammer. rewrite A4, BC, Cycles. lia.

    (* 0x800013c8 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A5 [A2 [A4 [BR0 Cycles]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A4, BC, Cycles. lia.

    (* 0x800013d0 *)
    destruct PRE as [mem [gp [MEM [GP [A2 [A3 [A5 [NotSuspended [Br Cycles]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A3, Cycles, BC. lia.

    (* 0x800013d8 *)
    destruct PRE as [mem [gp [MEM [GP [A3 [A4 [A5 [B1 [B2 [NotSuspended Cycles]]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step.
        handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A3, A4, BC, Cycles. lia.

    (* 0x800013e0 *)
    destruct PRE as [mem [gp [MEM [GP [A3 [A4 [A5 [B1 [B2 [B3 [NotSuspended Cycles]]]]]]]]]]].
    step.
        admit. (* Internals of __clzsi2 *)
    (* Inside vApplicationStackOverflowHook *)
    step. step. step. step. step. step. step. step. step. step. exact I.

    (* 0x8000142c *)
    destruct PRE as [mem [gp [MEM [GP [A2 [A3 [A4 [A5 [NotSuspended Cycles]]]]]]]]].
    step. step. step. step. step. step. step. step. step. step. step.
        eexists. exists gp, (4 + mem â¹[ 4 + mem â¹[ 4 + mem â¹[ 48 + pxCurrentTCB gp mem ] ] ]),
            (mem â¹[ 12 + mem â¹[ 48 + pxCurrentTCB gp mem ] ]).
        repeat split.
        unfold timing_postcondition.
        replace (uxSchedulerSuspended gp _ =? 0) with true.
        psimpl. apply Bool.negb_true_iff in BC. rewrite BC.
        hammer. rewrite A2, A5, BC, Cycles.
        psimpl. cbn [negb]. lia.
        admit. (* noverlap *)
    step. step. step. step. step. step. step. step. step. step. step.
    step.
        eexists. exists gp, (4 + mem â¹[ 4 + mem â¹[ 4 + mem â¹[ 48 + pxCurrentTCB gp mem ] ] ]),
            (mem â¹[ 12 + mem â¹[ 48 + pxCurrentTCB gp mem ] ]).
        repeat split.
        unfold timing_postcondition.
        replace (uxSchedulerSuspended gp _ =? 0) with true.
        apply Bool.negb_false_iff in BC. rewrite BC.
        hammer. rewrite A2, A5, BC, Cycles. cbn [negb]. lia.
        admit. (* noverlap *)

    step. exact I.

    Unshelve. exact 0. exact 0.
Admitted.

