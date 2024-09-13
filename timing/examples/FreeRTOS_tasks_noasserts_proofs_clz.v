Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import memsolve.

Definition start_vTaskSwitchContext : N := 0x8000137c.
Definition end_vTaskSwitchContext : N := 0x8000144c.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
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
    gp ⊖ 924.

Definition vTaskSwitchContext_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x8000138c | 0x8000144c => true
  | _ => false
  end | _ => false end.

(* TODO : Rewrite postconditions, the if conditions are garbage from earlier versions *)
Definition timing_postcondition (t : trace) (gp : N) (mem : addr -> N) : Prop :=
    if (uxSchedulerSuspended gp mem) =? 0 then
        cycle_count_of_trace t = 25 + 3 * time_branch + 17 * time_mem
        + (if (4 + mem Ⓓ[ 4 + mem Ⓓ[ 4 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ]])
            =? (mem Ⓓ[ 12 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ])
            then 22 + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 5 * time_mem else
            19 + time_branch + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 3 * time_mem
        )
    else
        cycle_count_of_trace t = 5 + time_branch + 2 * time_mem.

Definition __global_pointer : N := 0x80080800.
Definition __global_size : N := 2048.
Definition __stack_pointer : N :=
    (* Section 4.4.2. RAM Layout - 
        The stack starts at the very end of the RAM at address ORIGIN(ram) + LENGTH(ram) - 4.
        The stack grows downwards.*)
    (* https://cdn.hackaday.io/files/1741677451560928/NEORV32.pdf *)
    (2 ^ 32) - 4.

Definition vTaskSwitchContext_stack_frame_size : N := 16.

Definition gp_sp_noverlap (gp sp : N) : Prop :=
    ~overlap 32 (gp ⊖ __global_size) __global_size (sp ⊖ vTaskSwitchContext_stack_frame_size) vTaskSwitchContext_stack_frame_size.

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

Definition pxCurrentTCB_noverlap_static (gp : N) mem : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (48 + pxCurrentTCB gp mem) 4
            (gp ⊖ x) len_x.

Definition pxCurrentTCB_noverlap_stackframe (gp base_sp : N) mem : Prop :=
    ~ overlap 32
        (48 + pxCurrentTCB gp mem) 4
        (base_sp ⊖ 16) 16.

Definition mem_pxCurrentTCB_noverlap_stackframe (gp base_sp : N) mem : Prop :=
    ~ overlap 32
        (mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
        (base_sp ⊖ 16) 16.

Definition mem_pxCurrentTCB_noverlap_static (gp : N) mem : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
            (gp ⊖ x) len_x.

Definition vTaskSwitchContext_timing_invs (_ : store) (p : addr) (base_sp : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    (* vApplicationStackOverflowHook *)
    (* NOTE : This function intentionally goes into an infinite loop when a
       stack overflow is detected.
        https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC/main.c#L192
    *)
    | 0x8000e804 => Some True
    (* vTaskSwitchContext *)
    | 0x80001380 => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ s R_SP = Ⓓbase_sp 
            /\ s R_A4 = Ⓓ(uxSchedulerSuspended gp mem) /\
            gp_sp_noverlap gp base_sp /\
            smem_well_formed gp /\
            pxCurrentTCB_noverlap_static gp mem /\
            pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
            mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
            mem_pxCurrentTCB_noverlap_static gp mem /\
        cycle_count_of_trace t' = time_mem)
    | 0x800013b4 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ((0xa5a5a << 12) + 1445) /\
        gp_sp_noverlap gp base_sp /\
        smem_well_formed gp /\
        pxCurrentTCB_noverlap_static gp mem /\
        pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_static gp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 7 * time_mem + time_branch)
    | 0x800013bc => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        gp_sp_noverlap gp base_sp /\
        smem_well_formed gp /\
        pxCurrentTCB_noverlap_static gp mem /\
        pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_static gp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        cycle_count_of_trace t' = 9 + 8 * time_mem + time_branch)
    | 0x800013c4 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        gp_sp_noverlap gp base_sp /\
        smem_well_formed gp /\
        pxCurrentTCB_noverlap_static gp mem /\
        pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_static gp mem /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        (mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] =? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) = true /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 12 + 9 * time_mem + time_branch
    )
    | 0x800013cc => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        gp_sp_noverlap gp base_sp /\
        smem_well_formed gp /\
        pxCurrentTCB_noverlap_static gp mem /\
        pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_static gp mem /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        (mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] =? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) = true /\
        (mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]] =? mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) = true /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 15 + 10 * time_mem + time_branch
    )
    | 0x80001418 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A1 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[(gp ⊖ 920) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]]) /\
        s R_A2 = Ⓓ(addr_pxReadyTasksLists gp ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)) /\
        s R_A3 = Ⓓ(31 ⊖ clz (uxTopReadyPriority gp mem) 32) /\
        s R_A4 = Ⓓ(addr_pxReadyTasksLists gp) /\
        s R_A5 = Ⓓ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) /\
        gp_sp_noverlap gp base_sp /\
        smem_well_formed gp /\
        pxCurrentTCB_noverlap_static gp mem /\
        pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
        mem_pxCurrentTCB_noverlap_static gp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 36 + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 2 * time_branch + 14 * time_mem)
    | 0x8000138c => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ timing_postcondition t gp mem)
    | 0x8000144c => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        timing_postcondition t gp mem)
    | _ => None end
| _ => None
end.

Definition lifted_vTaskSwitchContext : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

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

(*
Define some function f
- f takes in index into GP 
- f returns length of buffer that is at mem(gp - index) (or none if malformed)
Assume in theorem that (forall x y, (assume f x, f y are Some number) 
    x <> y -> ~ overlap (gp - x) (f x) (gp - y) (f y) )
Assume (forall x, exists k, f x = Some k -> ~ overlap (gp - x) (f x) (sp (-) 16 16 ))
Now we can specialize assumption for pxcurrenttcb, uxschedulersuspended etc.

Do we assume that these buffers don't overlap with stack frame?
*)

Theorem clz_le_w : forall n w,
    clz n w <= w.
Proof.
    destruct n; intros; unfold clz; lia.
Qed.

Theorem vTaskSwitchContext_timing:
  forall s p t s' x' gp sp mem
         (ENTRY: startof t (x',s') = (Addr start_vTaskSwitchContext,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (GP : s R_GP = Ⓓgp)
         (SP : s R_SP = Ⓓsp)
         (MEM : s V_MEM32 = Ⓜmem)
         (GP_SP_FAR : gp_sp_noverlap gp sp)
         (PCT_NOL_STATIC : pxCurrentTCB_noverlap_static gp mem)
         (PCT_NOL_SFRAME : pxCurrentTCB_noverlap_stackframe gp sp mem)
         (MEM_PCT_NOL_SFRAME : mem_pxCurrentTCB_noverlap_stackframe gp sp mem)
         (MEM_PCT_NOL_STATIC : mem_pxCurrentTCB_noverlap_static gp mem)
         (SMEM_WELL_FORMED : smem_well_formed gp)
         (* (TCB_STACK_NO : ~ overlap 32 (pxCurrentTCB gp mem) 52 (sp ⊖ 16) 16) *)
         ,
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
    Ltac noverlap_prepare gp sp :=
        _noverlap_prepare uxSchedulerSuspended pxCurrentTCB 
            gp_sp_noverlap __global_size vTaskSwitchContext_stack_frame_size 
            gp sp.

    (* Base case *)
    simpl. rewrite ENTRY. step.
    exists mem, gp. repeat split; try assumption.
    unfold uxSchedulerSuspended. unfold msub. psimpl. reflexivity.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* 0x800015e4 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A4 [GP_SP_FAR [SMEM_WELL_FORMED 
        [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC 
        Cycles]]]]]]]]]]]].
    step. step. step. step. step. step. step. step. step. step.
    do 2 eexists. repeat split. unfold msub. now psimpl.
        {
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l with (a := 4294965400 + gp);
            replace (4294965400 ⊕ gp) with (gp ⊖ 1896) by 
                (unfold msub; psimpl; lia).
            memsolve mem gp sp; 
            try solve [ now (
                apply PCT_NOL_STATIC ||
                apply PCT_NOL_SFRAME
            )].
            all: apply noverlap_symmetry;
                (apply noverlap_shrink with (sp ⊖ 16) 16;
                    [ psimpl; lia | apply noverlap_symmetry]);
                assumption.
        }
        {
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l with (a := 4294965400 + gp);
            replace (4294965400 ⊕ gp) with (gp ⊖ 1896) by 
                (unfold msub; psimpl; lia).
            memsolve mem gp sp;
            try solve [ now (
                apply PCT_NOL_STATIC ||
                apply PCT_NOL_SFRAME ||
                apply MEM_PCT_NOL_STATIC
            )].
            all: try solve [apply noverlap_symmetry;
                (apply noverlap_shrink with (sp ⊖ 16) 16;
                    [ psimpl; lia | apply noverlap_symmetry]);
                assumption].
        } assumption. assumption.
        {
            unfold pxCurrentTCB_noverlap_static in *.
            intros. noverlap_prepare gp sp. memsolve mem gp sp.
            apply PCT_NOL_STATIC, H.
        }
        {
            unfold pxCurrentTCB_noverlap_stackframe in *.
            intros. noverlap_prepare gp sp. memsolve mem gp sp.
            apply PCT_NOL_SFRAME.
        }
        {
            unfold mem_pxCurrentTCB_noverlap_stackframe in *.
            intros. noverlap_prepare gp sp. memsolve mem gp sp.
                apply MEM_PCT_NOL_SFRAME.
                now apply PCT_NOL_STATIC.
                all: apply noverlap_symmetry, noverlap_shrink with (sp ⊖ 16) 16;
                    [ psimpl; lia |
                      apply noverlap_symmetry, PCT_NOL_SFRAME ].
        }
        {
            unfold mem_pxCurrentTCB_noverlap_static in *.
            intros. noverlap_prepare gp sp. memsolve mem gp sp.
                now apply MEM_PCT_NOL_STATIC.
                now apply PCT_NOL_STATIC.
                all: apply noverlap_symmetry, noverlap_shrink with (sp ⊖ 16) 16;
                    [ psimpl; lia |
                      apply noverlap_symmetry, PCT_NOL_SFRAME ].
        }
        { noverlap_prepare gp sp. memsolve mem gp sp. assumption. }
        hammer. rewrite A4, BC, Cycles. lia.
    step. step. handle_ex.
        unfold timing_postcondition. unfold uxSchedulerSuspended in *.
            rewrite getmem_frame; try (left; psimpl; lia).
        rewrite BC.
        hammer. rewrite A4, BC, Cycles. lia.

    (* 0x800013c8 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A5 [A2 [A4 [GP_SP_FAR [SMEM_WELL_FORMED 
        [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC 
        [BR0 Cycles]]]]]]]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A4, BC, Cycles. lia.

    (* 0x800013d0 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A2 [A3 [A5 [GP_SP_FAR [SMEM_WELL_FORMED 
        [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC 
        [NotSuspended [Br Cycles]]]]]]]]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A3, Cycles, BC. lia.

    (* 0x800013d8 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A3 [A4 [A5 [GP_SP_FAR [SMEM_WELL_FORMED 
        [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC 
        [B1 [B2 [NotSuspended Cycles]]]]]]]]]]]]]]]]].
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step.
        handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A3, A4, BC, Cycles. lia.

    (* 0x800013e0 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A3 [A4 [A5 [GP_SP_FAR [SMEM_WELL_FORMED 
        [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC 
        [B1 [B2 [B3 [NotSuspended Cycles]]]]]]]]]]]]]]]]]].
    step. step. step. step. step. step. step. step. step. step. step.
    step. step. step. step.
        handle_ex. repeat split.
        {
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l with (a := 4294965376 + gp);
            replace (4294965376 ⊕ gp) with (gp ⊖ 1920) by 
                (unfold msub; psimpl; lia).
            rewrite <- getmem_mod_l with (a := 4294966376 + gp + 
                (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20).
            replace (mem Ⓓ[ 4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ])
            with (mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]); cycle 7.
            unfold msub at 1. now psimpl. unfold uxTopReadyPriority.
            memsolve mem gp sp; unfold msub at 1; psimpl.
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊖ 1920 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
            admit. (* actual overlaps *)
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊖ 1920 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
            admit. (* Don't even know what's going on here *)
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊖ 1920 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
            admit. (* actual overlaps *)
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊖ 1920 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold addr_pxReadyTasksLists, uxTopReadyPriority.
            noverlap_prepare gp sp; memsolve mem gp sp. f_equal.
                unfold msub; psimpl.
                replace (2 ^ 32 - 1920 mod 2 ^ 32) with 4294965376 by reflexivity.
                now rewrite getmem_mod_l, (N.add_comm gp).
            unfold msub at 1; psimpl.
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold uxTopReadyPriority.
            noverlap_prepare gp sp; memsolve mem gp sp.
                unfold msub at 3. simpl (_ - _ mod _).
                now rewrite getmem_mod_l, (N.add_comm 4294965376).
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        now unfold addr_pxReadyTasksLists, msub; psimpl.
        {
            unfold uxTopReadyPriority.
            noverlap_prepare gp sp; memsolve mem gp sp. f_equal.
                unfold msub at 2 4. simpl (_ - _ mod _).
                rewrite N.add_comm, N.add_assoc.
                rewrite (N.add_comm _ gp), getmem_mod_l. now psimpl.
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold pxCurrentTCB_noverlap_static. intros.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply PCT_NOL_STATIC.
            unfold msub at 1. simpl (_ - _ mod _).
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold pxCurrentTCB_noverlap_stackframe. intros.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply PCT_NOL_SFRAME.
            unfold msub at 1. simpl (_ - _ mod _).
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold mem_pxCurrentTCB_noverlap_stackframe.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply MEM_PCT_NOL_SFRAME.
            all: unfold msub at 1; simpl (_ - _ mod _);
            try (apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia).
            admit. (* Deeper CLZ noverlap *)
        }
        {
            unfold mem_pxCurrentTCB_noverlap_static. intros.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply MEM_PCT_NOL_STATIC.
            all: unfold msub at 1; simpl (_ - _ mod _);
            try (apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia).
            admit. (* Deeper CLZ noverlap *)
        }
        {
            noverlap_prepare gp sp; memsolve mem gp sp.
            assumption.
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        hammer. rewrite A4, A5, BC, Cycles. psimpl.
        (* Can't infer placeholder? *)
        replace ((mem[Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20
                    := mem Ⓓ[ 4 + mem Ⓓ[ 4294966376 + gp + 
                                (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20 ]
                            ] 
                    ]) Ⓓ[ 4294965376 + gp ]) with (mem Ⓓ[ 4294965376 + gp ]).
        lia.
        {
            noverlap_prepare gp sp. memsolve mem gp sp.
            apply sep_noverlap; left; psimpl; admit. (* CLZ noverlap *)
        }
    (* Inside vApplicationStackOverflowHook *)
    step. step. step. step. step. step. step. step. step. step. exact I.

    (* 0x8000142c *)
    destruct PRE as [mem [gp [MEM [GP [SP [A1 [A2 [A3 [A4 [A5 [GP_SP_FAR 
        [SMEM_WELL_FORMED [PCT_NOL_STATIC [PCT_NOL_SFRAME [MEM_PCT_NOL_SFRAME
        [MEM_PCT_NOL_STATIC [NotSuspended Cycles]]]]]]]]]]]]]]]]].
    step. step. step. step. step. step. step. step. step. step. step.
        handle_ex.
        {
            (* noverlap_prepare gp sp. memsolve mem gp sp. *)
            (* There actually is an overlapping case here. Too overzealous
               with getmem_noverlap? *)
            admit.
        }
        unfold timing_postcondition.
        replace (uxSchedulerSuspended gp _ =? 0) with true.
        apply Bool.negb_true_iff in BC. (* rewrite BC. *)
        hammer. rewrite A1, A5, BC, Cycles.
        cbn [negb]. replace (_ =? _) with 
            (4 + mem Ⓓ[ 4 + mem Ⓓ[ 4 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] ] =?
            mem Ⓓ[ 12 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ]).
        rewrite BC. replace (
            clz ((mem [Ⓓ4294965400 + gp
                := mem
                Ⓓ[ 12 +
                    mem
                    Ⓓ[ 4 + mem Ⓓ[ 8 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] +
                        mem Ⓓ[ 4 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] * 20 ] ] ])
            Ⓓ[ 4294965376 + gp ]) 32
                    ) with (clz (mem Ⓓ[ 4294965376 + gp ]) 32).
        lia.
        noverlap_prepare gp n; memsolve mem gp n.
        { admit. (* More actual overlapping stuff *)}
        { unfold uxSchedulerSuspended. noverlap_prepare gp n. memsolve mem gp n.
          now rewrite NotSuspended. }
    step. step. step. step. step. step. step. step. step. step. step.
    step.
        handle_ex.
        { admit. (* More actual overlapping stuff *) }
        unfold timing_postcondition.
        replace (uxSchedulerSuspended gp _ =? 0) with true.
        apply Bool.negb_false_iff in BC.
        hammer. rewrite A1, A5, BC, Cycles.
        match goal with
        | [H: (?a =? ?b) = true |- _ = (if ?x =? ?y then _ else _) ] =>
            replace (x =? y) with (a =? b); [rewrite H|idtac]
        | _ => idtac end.
        cbn [negb].
        replace (clz
        ((mem [Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
            := mem Ⓓ[ 4294966384 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ] ]
            [Ⓓ4294965400 + gp
            := (mem [Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                := mem Ⓓ[ 4294966384 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                ] ])
            Ⓓ[ 12 +
                (mem [Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                := mem
                    Ⓓ[ 4294966384 + gp + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]
                ])
                Ⓓ[ 4 + mem Ⓓ[ 8 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] +
                    mem Ⓓ[ 4 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] * 20 ] ] ])
        Ⓓ[ 4294965376 + gp ]) 32) with (clz (mem Ⓓ[ 4294965376 + gp ]) 32).
        lia.
        { f_equal. noverlap_prepare gp sp. memsolve mem gp sp.
            admit. (* CLZ noverlap *)
        }
        { admit. (* More actual overlapping stuff *) }
        { noverlap_prepare gp n0. memsolve mem gp n0. now rewrite NotSuspended.
          admit. (* CLZ noverlap *) }

    step. exact I.
Admitted.

