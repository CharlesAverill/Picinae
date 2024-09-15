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
    (* TODO : Prove that smem_well_formed doesn't break with this in it *)
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

Definition pxCurrentTCB_noverlap_clz_static (gp : N) mem : Prop :=
    ~ overlap 32
        (48 + pxCurrentTCB gp mem) 4
        (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20) 4.

Definition clz_noverlap_smem (gp : N) mem : Prop :=
    forall x len_x,
        static_buffer_lengths_in_bytes x = Some len_x ->
        ~ overlap 32
            (gp ⊖ x) len_x
            (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20) 4.

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

Definition offset_mem_pxCurrentTCB_noverlap_clz (gp : N) mem : Prop :=
    forall k, k = 8 \/ k = 12 ->
        ~ overlap 32
            (k + mem Ⓓ[48 + pxCurrentTCB gp mem]) 4
            (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20) 4.

Definition common_noverlaps gp base_sp mem : Prop :=
    gp_sp_noverlap gp base_sp /\
    smem_well_formed gp /\
    pxCurrentTCB_noverlap_static gp mem /\
    pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
    pxCurrentTCB_noverlap_clz_static gp mem /\
    clz_noverlap_smem gp mem /\
    mem_pxCurrentTCB_noverlap_stackframe gp base_sp mem /\
    mem_pxCurrentTCB_noverlap_static gp mem /\
    offset_mem_pxCurrentTCB_noverlap_clz gp mem.

(* TODO : Rewrite postconditions, the if conditions are garbage from earlier versions *)
Definition timing_postcondition (t : trace) (gp : N) (mem : addr -> N) : Prop :=
    if (uxSchedulerSuspended gp mem) =? 0 then
        cycle_count_of_trace t = 25 + 3 * time_branch + 17 * time_mem
        + (if (mem Ⓓ[(gp ⊖ 920) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)])
            =? ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20)
            then 22 + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 5 * time_mem else
            19 + time_branch + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 3 * time_mem
        )
    else
        cycle_count_of_trace t = 5 + time_branch + 2 * time_mem.

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
            common_noverlaps gp base_sp mem /\
        cycle_count_of_trace t' = time_mem)
    | 0x800013b4 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ((0xa5a5a << 12) + 1445) /\
        common_noverlaps gp base_sp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 6 + 7 * time_mem + time_branch)
    | 0x800013bc => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A2 = Ⓓ(mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        common_noverlaps gp base_sp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        cycle_count_of_trace t' = 9 + 8 * time_mem + time_branch)
    | 0x800013c4 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A3 = Ⓓ(mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A4 = Ⓓ(mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\
        s R_A5 = Ⓓ(mem Ⓓ[48 + pxCurrentTCB gp mem]) /\
        common_noverlaps gp base_sp mem /\
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
        common_noverlaps gp base_sp mem /\
        (mem Ⓓ[ mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =? 0xa5a5a5a5) = true /\
        (mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]] =? mem Ⓓ[mem Ⓓ[48 + pxCurrentTCB gp mem]]) = true /\
        (mem Ⓓ[8 + mem Ⓓ[48 + pxCurrentTCB gp mem]] =? mem Ⓓ[4 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) = true /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        cycle_count_of_trace t' = 15 + 10 * time_mem + time_branch
    )
    | 0x80001418 => Some (exists mem gp, s V_MEM32 = Ⓜmem /\ 
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        s R_A1 = Ⓓ(mem Ⓓ[4 + (gp ⊖ 924) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]) /\
        s R_A2 = Ⓓ(addr_pxReadyTasksLists gp ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)) /\
        s R_A3 = Ⓓ(31 ⊖ clz (uxTopReadyPriority gp mem) 32) /\
        s R_A4 = Ⓓ(addr_pxReadyTasksLists gp) /\
        s R_A5 = Ⓓ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) /\
        common_noverlaps gp base_sp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        (mem Ⓓ[ 12 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ] =?
            mem Ⓓ[ 8 + mem Ⓓ[ 48 + pxCurrentTCB gp mem ] ]) = true /\
        cycle_count_of_trace t' = 36 + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 2 * time_branch + 14 * time_mem)
    | 0x80001424 => Some (exists mem' mem gp, s V_MEM32 = Ⓜmem /\
        s R_GP = Ⓓgp /\ s R_SP = Ⓓ(base_sp ⊖ 16) /\
        (* s R_A1 = Ⓓ(mem Ⓓ[4 + (gp ⊖ 924) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]) /\ *)
        s R_A2 = Ⓓ(addr_pxReadyTasksLists gp ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)) /\
        s R_A3 = Ⓓ(31 ⊖ clz (uxTopReadyPriority gp mem) 32) /\
        s R_A4 = Ⓓ(addr_pxReadyTasksLists gp) /\
        (* s R_A5 = Ⓓ((gp ⊖ 916) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem) 32) * 20) /\ *)
        common_noverlaps gp base_sp mem /\
        (uxSchedulerSuspended gp mem =? 0) = true /\
        match (negb (mem' Ⓓ[ 4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20 ] =?
            gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20)) with
        | false => mem Ⓓ[(gp ⊖ 920) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)] 
            = mem Ⓓ[(gp ⊖ 912) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]
        | true => mem = mem'
        end /\
        (* (negb (mem' Ⓓ[ 4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20 ] =?
         gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20) = false ->
         mem Ⓓ[(gp ⊖ 920) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)] 
            = mem Ⓓ[(gp ⊖ 912) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem) 32)) * 20)]) /\ *)
        cycle_count_of_trace t' = 36 + clz (mem Ⓓ[ 4294965376 + gp ]) 32 + 2 * time_branch + 14 * time_mem + 
            (
                if negb 
                    (mem' Ⓓ[4 + (gp ⊖ 924) ⊕ ((31 ⊖ (clz (uxTopReadyPriority gp mem') 32)) * 20)] 
                        =? 
                    (gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20))
                then
                    time_branch
                else
                    3 + 2 * time_mem
            ))
    | 0x8000138c => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\ 
        timing_postcondition t gp mem)
    | 0x8000144c => Some (
        exists mem gp, s V_MEM32 = Ⓜmem /\ s R_GP = Ⓓgp /\
        (* s R_A5 = Ⓓ(mem Ⓓ[12 + mem Ⓓ[48 + pxCurrentTCB gp mem]]) /\ *)
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
         (NOVERLAPS : common_noverlaps gp sp mem)
         (* (GP_SP_FAR : gp_sp_noverlap gp sp)
         (PCT_NOL_STATIC : pxCurrentTCB_noverlap_static gp mem)
         (PCT_NOL_SFRAME : pxCurrentTCB_noverlap_stackframe gp sp mem)
         (MEM_PCT_NOL_SFRAME : mem_pxCurrentTCB_noverlap_stackframe gp sp mem)
         (MEM_PCT_NOL_STATIC : mem_pxCurrentTCB_noverlap_static gp mem)
         (SMEM_WELL_FORMED : smem_well_formed gp) *)
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
    Local Ltac noverlap_prepare gp sp :=
        _noverlap_prepare uxSchedulerSuspended pxCurrentTCB 
            gp_sp_noverlap __global_size vTaskSwitchContext_stack_frame_size 
            gp sp.
    Local Ltac destruct_noverlaps :=
        match goal with
        | [H: common_noverlaps _ _ _ |- _] =>
            destruct H as [GP_SP_FAR [SMEM_WELL_FORMED [PCT_NOL_STATIC 
            [PCT_NOL_SFRAME [PCT_NOL_CLZ [CLZ_NOL_STATIC 
            [MEM_PCT_NOL_SFRAME [MEM_PCT_NOL_STATIC OFF_MEM_PCT_NOL_CLZ]]]]]]]]
        end.
    destruct_noverlaps.

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
    destruct PRE as [mem [gp [MEM [GP [SP [A4 [NOVERLAPS Cycles]]]]]]].
        destruct_noverlaps.
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
            unfold pxCurrentTCB_noverlap_clz_static in *.
            noverlap_prepare gp sp; memsolve mem gp sp.
            assumption.
        }
        {
            unfold clz_noverlap_smem in *. intros.
            noverlap_prepare gp sp; memsolve mem gp sp.
            eapply CLZ_NOL_STATIC. eassumption.
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
        } {
            unfold offset_mem_pxCurrentTCB_noverlap_clz. intros.
            noverlap_prepare gp sp. memsolve mem gp sp.
                now apply OFF_MEM_PCT_NOL_CLZ.
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
    destruct PRE as [mem [gp [MEM [GP [SP [A5 [A2 [A4 [NOVERLAPS [BR0 Cycles]]]]]]]]]].
        destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex. change ((678490 << 12) + 1445) with 0xa5a5a5a5 in *.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A4, BC, Cycles. lia.

    (* 0x800013d0 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A2 [A3 [A5 [NOVERLAPS [NotSuspended 
        [Br Cycles]]]]]]]]]]]. destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step. handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A2, A3, Cycles, BC. lia.

    (* 0x800013d8 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A3 [A4 [A5 [NOVERLAPS
        [B1 [B2 [NotSuspended Cycles]]]]]]]]]]]]. destruct_noverlaps.
    step.
        step. step. step. step. step. step. step. step. step. step.
        exact I. (* Infinite loop, stack overflow detected *)
    step.
        handle_ex.
        now apply Bool.negb_false_iff in BC.
        hammer. rewrite A3, A4, BC, Cycles. lia.

    (* 0x800013e0 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A3 [A4 [A5 [NOVERLAPS [B1 [B2 [B3 
        [NotSuspended Cycles]]]]]]]]]]]]]. destruct_noverlaps.
    step. step. step. step. step. step. step. step. step. step. step.
    step. step. step. step.
        handle_ex.
        {
            unfold uxTopReadyPriority.
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l with (a := 4294965376 + gp);
            replace (4294965376 ⊕ gp) with (gp ⊖ 1920) by 
                (unfold msub; psimpl; lia).
            rewrite <- getmem_mod_l with (a := 4294966376 + gp + 
                (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20).
            replace (mem Ⓓ[ 4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ])
            with (mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]); cycle 7.
                unfold msub at 1; now psimpl.
            rewrite <- setmem_mod_l, (N.add_comm 4294966376).
            assert (forall n, gp + 4294966376 ⊕ n = gp ⊖ 920 ⊕ n). {
                intros. unfold msub. simpl (_ - _ mod _).
                now psimpl.
            } rewrite H. clear H.
            assert (forall n, 4 + (gp ⊖ 924) ⊕ n = (gp ⊖ 920) ⊕ n).
                intros; unfold msub; simpl (_ - _ mod _); now psimpl.
            rewrite H. clear H. psimpl.
            replace (clz
            ((mem [Ⓓgp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
              := mem
                 Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]
                 ] ]) Ⓓ[ gp ⊖ 1920 ]) 32) with 
                (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32); cycle 1. {
                f_equal. memsolve mem gp sp.
                apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊖ 1920 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
            } psimpl. reflexivity.
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
            unfold pxCurrentTCB_noverlap_clz_static.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply PCT_NOL_CLZ.
            all: unfold msub at 1; simpl (_ - _ mod _);
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
        {
            unfold clz_noverlap_smem in *. intros.
            replace ((mem
            [Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20
            := mem
               Ⓓ[ 4 +
                  mem
                  Ⓓ[ 4294966376 + gp +
                     (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20 ] ] ])
           Ⓓ[ gp ⊖ 1920 ]) with (mem Ⓓ[gp ⊖ 1920]).
           eapply CLZ_NOL_STATIC. eassumption.
           rewrite <- setmem_mod_l.
           rewrite <- getmem_mod_l with (a := 4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20).
           rewrite getmem_noverlap. reflexivity.
           rewrite <- getmem_mod_l. 
           replace (mem Ⓓ[ 4294965376 ⊕ gp ]) with (mem Ⓓ[ gp ⊖ 1920 ]) by (unfold msub; psimpl; lia).
           replace (4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20) with
                (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20).
           now eapply CLZ_NOL_STATIC.
           now unfold msub at 1; psimpl.
        }
        {
            unfold mem_pxCurrentTCB_noverlap_stackframe.
            replace (mem Ⓓ[ 4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20 ])
                with (mem Ⓓ[ (gp ⊖ 920) + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]).
            replace (mem [Ⓓ4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20
                := mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]]])
                with (mem [Ⓓ(gp ⊖ 920) + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20
                := mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]]]).
            rewrite <- setmem_mod_l.
            noverlap_prepare gp sp; memsolve mem gp sp.
            now apply MEM_PCT_NOL_SFRAME.
            all: try solve [unfold msub at 1; simpl (_ - _ mod _);
                apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia].
            replace (mem Ⓓ[ 4294965376 + gp ]) with (mem Ⓓ[gp ⊖ 1920]) by 
                (unfold msub; simpl (_ - _ mod _); psimpl; lia).
            apply PCT_NOL_CLZ.
            unfold msub at 1. simpl (_ - _ mod _).
                rewrite <- setmem_mod_l with 
                    (a := gp ⊕ 4294966376 + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20).
                rewrite <- setmem_mod_l with
                    (a := 4294966376 + gp + (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20).
                now psimpl.
            unfold msub at 1 3; simpl (_ - _ mod _).
                rewrite getmem_mod_l; psimpl.
                now rewrite (N.add_comm gp).
        }
        {
            unfold mem_pxCurrentTCB_noverlap_static. intros.
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l with (a := 4294965376 + gp);
            replace (4294965376 ⊕ gp) with (gp ⊖ 1920) by 
                (unfold msub; psimpl; lia).
            rewrite <- getmem_mod_l with (a := 4294966376 + gp + 
                (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20).
            replace (mem Ⓓ[ 4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ])
            with (mem Ⓓ[ gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ]); cycle 7.
                unfold msub at 1; now psimpl.
            rewrite <- setmem_mod_l, (N.add_comm 4294966376).
            assert (forall n, gp + 4294966376 ⊕ n = gp ⊖ 920 ⊕ n).
                intros; unfold msub; simpl (_ - _ mod _);
                now psimpl.
            rewrite H0. clear H0. psimpl.
            replace ((mem [Ⓓgp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                := mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ] ] ])
            Ⓓ[ 48 +
                (mem [Ⓓgp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                := mem Ⓓ[ 4 + mem Ⓓ[ gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ] ] ])
                Ⓓ[ gp ⊖ 1896 ] ]) with (mem Ⓓ[48 + pxCurrentTCB gp mem]).
            now apply MEM_PCT_NOL_STATIC.
            rewrite <- setmem_mod_l with (a := gp ⊖ 920 + (31 ⊖ clz (mem Ⓓ[ gp ⊖ 1920 ]) 32) * 20).
            memsolve mem gp sp. reflexivity.
            (* unfold msub at 1 4; simpl (_ - _ mod _). *)
            all: try solve [unfold msub at 1 4; simpl (_ - _ mod _);
                apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ gp ⊕ 4294965376 ]) 32);
                remember (clz (mem Ⓓ[ gp ⊕ 4294965376 ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia].
            assumption.
        } {
            unfold offset_mem_pxCurrentTCB_noverlap_clz. intros.
            noverlap_prepare gp sp. rewrite <- setmem_mod_l.
            memsolve mem gp sp;
                try replace (4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20) with
                    (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20) by 
                    (unfold msub; now psimpl);
                replace (mem Ⓓ[ 4294965376 + gp ]) with (mem Ⓓ[ gp ⊖ 1920 ]) by
                    (unfold msub; now psimpl).
                now apply OFF_MEM_PCT_NOL_CLZ.
            all: try now apply CLZ_NOL_STATIC.
            apply PCT_NOL_CLZ.
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
        } {
            rewrite <- setmem_mod_l.
            noverlap_prepare gp sp.
            memsolve mem gp sp;
                try replace (4294966376 + gp ⊕ (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20) with
                    (gp ⊖ 920 ⊕ (31 ⊖ clz (mem Ⓓ[ 4294965376 + gp ]) 32) * 20) by 
                    (unfold msub; now psimpl);
                replace (mem Ⓓ[ 4294965376 + gp ]) with (mem Ⓓ[ gp ⊖ 1920 ]) by
                    (unfold msub; now psimpl); auto.
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
            apply sep_noverlap; left; psimpl;
                pose proof (clz_le_w (mem Ⓓ[ 4294965376 + gp ]) 32);
                remember (clz (mem Ⓓ[ 4294965376 + gp ]) 32) as n; clear Heqn;
                do 33 (destruct n as [| n _] using N.peano_ind;
                    [cbn [N.succ Pos.succ]; psimpl; lia|
                    replace (N.succ n) with (1 + n) in H by lia; psimpl in H]);
                lia.
        }
    (* Inside vApplicationStackOverflowHook *)
    step. step. step. step. step. step. step. step. step. step. exact I.

    (* 0x80001418 *)
    destruct PRE as [mem [gp [MEM [GP [SP [A1 [A2 [A3 [A4 [A5 [NOVERLAPS 
        [NotSuspended [B1 Cycles]]]]]]]]]]]]]. destruct_noverlaps.
    rename mem into mem'.
    step.
        exists mem'. handle_ex.
            now rewrite BC.
        hammer. rewrite getmem_mod_l, <- getmem_mod_l with (a := _ + _ + _).
        replace ((gp ⊖ 916 + (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20) mod 4294967296)
            with ((gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20)) by reflexivity.
        rewrite A1, A5, BC.
        rewrite Cycles. lia.
    step. step.
        exists mem'. handle_ex.
        {
            unfold uxTopReadyPriority, addr_pxReadyTasksLists.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp.
            replace (4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20) with
                ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20) by
                (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
        } {
            unfold uxTopReadyPriority, addr_pxReadyTasksLists.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp. assumption.
            replace (4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20) with
                ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20) by
                (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
        } {
            unfold pxCurrentTCB_noverlap_static, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp. now apply PCT_NOL_STATIC.
            replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                by (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
        } {
            unfold pxCurrentTCB_noverlap_stackframe, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp. apply PCT_NOL_SFRAME.
            replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                by (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
        } {
            unfold pxCurrentTCB_noverlap_clz_static, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl).
            apply PCT_NOL_CLZ.
            now apply CLZ_NOL_STATIC.
            now apply CLZ_NOL_STATIC.
        } {
            unfold clz_noverlap_smem, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
            now apply CLZ_NOL_STATIC.
        } {
            unfold mem_pxCurrentTCB_noverlap_stackframe, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl).
            apply MEM_PCT_NOL_SFRAME.
            now apply CLZ_NOL_STATIC.
            apply PCT_NOL_CLZ.
            now apply CLZ_NOL_STATIC.
        } {
            unfold mem_pxCurrentTCB_noverlap_static, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl).
            now apply MEM_PCT_NOL_STATIC.
            now apply CLZ_NOL_STATIC.
            apply PCT_NOL_CLZ.
            now apply CLZ_NOL_STATIC.
        } {
            unfold offset_mem_pxCurrentTCB_noverlap_clz, addr_pxReadyTasksLists,
                uxTopReadyPriority, pxCurrentTCB. intros.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl); auto.
        } {
            unfold uxSchedulerSuspended, 
                addr_pxReadyTasksLists, uxTopReadyPriority, pxCurrentTCB.
            rewrite <- setmem_mod_l.
            memsolve mem' gp sp;
                try replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                    by (unfold msub; now psimpl).
            assumption.
            now apply CLZ_NOL_STATIC.
        } {
            rewrite BC.
            rewrite <- setmem_mod_l, <- getmem_mod_l with (a := _ + _ + _).
            unfold addr_pxReadyTasksLists, uxTopReadyPriority. psimpl.
            unfold msub at 5. psimpl.
            replace ((mem' [Ⓓ4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20
                := mem' Ⓓ[ 12 + (gp ⊖ 924) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20 ] ])
                Ⓓ[ gp ⊖ 1920 ]) with (mem' Ⓓ[ gp ⊖ 1920 ]).
            psimpl. unfold msub. now psimpl.
                rewrite getmem_mod_l.
                replace (4294966384 + gp ⊕ (31 ⊕ (2 ^ 32 - clz (mem' Ⓓ[ gp ⊕ (2 ^ 32 - 1920 mod 2 ^ 32) ]) 32 mod 2 ^ 32)) * 20)
                with (gp ⊖ 912 ⊕ (31 ⊕ (2 ^ 32 - clz (mem' Ⓓ[ gp ⊕ (2 ^ 32 - 1920 mod 2 ^ 32) ]) 32 mod 2 ^ 32)) * 20).
                replace (gp ⊕ (2 ^ 32 - 916 mod 2 ^ 32)) with (gp ⊖ 916) by (unfold msub; now psimpl).
            rewrite getmem_noverlap. reflexivity.
            replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                by (unfold msub; now psimpl).
            now apply CLZ_NOL_STATIC.
            unfold msub. now psimpl.
        }
        hammer. rewrite A1, A5, BC, Cycles. rewrite getmem_mod_l in *.
        replace ((gp ⊖ 916 + (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20) mod 4294967296)
            with ((gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20)) by reflexivity.
        rewrite BC.
        replace ((mem' [Ⓓ4 + addr_pxReadyTasksLists gp + (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20
            := mem' Ⓓ[ 12 + addr_pxReadyTasksLists gp +
                (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20 ] ]) Ⓓ[ 4294965376 + gp ]) with
            (mem' Ⓓ[ gp ⊖ 1920 ]); cycle 1. {
            rewrite <- getmem_mod_l with (a := _ + _), <- setmem_mod_l.
            rewrite getmem_noverlap. now unfold msub; psimpl.
            replace (4294965376 ⊕ gp) with (gp ⊖ 1920) by
                (now unfold msub; psimpl).
            unfold addr_pxReadyTasksLists, uxTopReadyPriority.
            replace (4 + _ ⊕ _) with ((gp ⊖ 920) ⊕ (31 ⊖ clz (mem' Ⓓ[ gp ⊖ 1920 ]) 32) * 20)
                by (now unfold msub; psimpl).
            auto.
        } psimpl; unfold msub; simpl (_ - _); rewrite getmem_mod_l, (N.add_comm gp); psimpl; lia.

    destruct PRE as [mem' [mem [gp [MEM [GP [SP [A2 [A3 [A4 [NOVERLAPS [NotSuspended
        [BCPropagate Cycles]]]]]]]]]]]]. destruct_noverlaps.
    step. step. step. step. step. step. step. step. step. step.
        handle_ex. unfold timing_postcondition.
        replace (uxSchedulerSuspended gp _ =? 0) with true.
        hammer.
        destruct (negb (mem' Ⓓ[ 4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20 ] 
            =? gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20)) eqn:E.
        { subst.
            replace (_ =? _) with 
            (mem' Ⓓ[ 4 + (gp ⊖ 924) ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20 ] =?
                gp ⊖ 916 ⊕ (31 ⊖ clz (uxTopReadyPriority gp mem') 32) * 20).
            apply Bool.negb_true_iff in E. rewrite E.
            replace (mem' [Ⓓ _ := _] Ⓓ[ _ ]) with (mem' Ⓓ[ 4294965376 + gp ]).
            rewrite Cycles. psimpl. lia.
            now psimpl.
            unfold uxTopReadyPriority, addr_pxReadyTasksLists.
            rewrite <- setmem_mod_l.
            replace (4294965400 ⊕ gp) with (gp ⊖ 1896); cycle 1. {
                unfold msub. now psimpl.
            }
            rewrite <- getmem_mod_l with (a := _ + _ + _).
            rewrite <- getmem_mod_l with (a := _ ⊖ _ + _).
            (* rewrite <- setmem_mod_l with (a := _ + _ + _). *)
            repeat rewrite getmem_noverlap.
            unfold msub; now psimpl.
            apply SMEM_WELL_FORMED; auto. discriminate.
            apply noverlap_symmetry. auto.
            apply SMEM_WELL_FORMED; auto. discriminate.
        }
        match goal with [|- context[if ?A then _ else _]] => 
            replace A with true end.
        rewrite <- getmem_mod_l, <- setmem_mod_l.
        rewrite getmem_noverlap, Cycles. psimpl. rewrite getmem_mod_l. lia.
            replace (4294965376 ⊕ gp) with (gp ⊖ 1920) by
                (unfold msub; now psimpl).
            replace (4294965400 ⊕ gp) with (gp ⊖ 1896) by
                (unfold msub; now psimpl).
            apply SMEM_WELL_FORMED; auto. discriminate.
        {
            unfold uxTopReadyPriority, addr_pxReadyTasksLists in *.
            noverlap_prepare gp sp.
            rewrite <- getmem_mod_l.
            memsolve mem gp sp. admit.
            apply noverlap_symmetry. auto.
        }
        noverlap_prepare gp n; memsolve mem gp n. now rewrite NotSuspended.
    step. exact I.
Admitted.
