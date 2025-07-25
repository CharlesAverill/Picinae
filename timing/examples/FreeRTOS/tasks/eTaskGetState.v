Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module eTaskGetStateTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x80000958.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x800009e8 | 0x800009f0 => true
    | _ => false
  end | _ => false end.
End eTaskGetStateTime.

Module eTaskGetStateAuto := TimingAutomation eTaskGetStateTime.
Import eTaskGetStateTime eTaskGetStateAuto.

Definition pxCurrentTCB (gp : N) (mem : addr -> N) : N :=
    mem Ⓓ[gp ⊖ 1896].

Definition time_of_eTaskGetState (mem : addr -> N) (gp a3 : N) (xTask : addr) (t : trace) :=
  cycle_count_of_trace t =
    time_mem + 2 +
    if (pxCurrentTCB gp mem =? xTask) then (
      time_branch + 2 + time_branch
    ) else (
      3 + 3 + 2 * time_mem + 2 + 3 * time_mem +
      if (mem Ⓓ[0x80080004] =? 0) then (
        3 + 3
      ) else (
        time_branch
      ) +
      2 + 2 +
      if (xTask ⊕ 40 =? gp ⊖ 984) then (
        time_branch + time_branch
      ) else (
        3 + 2 +
        if (xTask ⊕ 20 =? mem Ⓓ[gp ⊖ 1900]) then (
          time_branch + time_branch
        ) else (
          3 + if (xTask ⊕ 20 =? mem Ⓓ[gp ⊖ 1904]) then (
            time_branch + time_branch
          ) else (
            3 + 2 + if (xTask ⊕ 20 =? gp ⊖ 1024) then (
              3 + time_mem + 
              if (xTask ⊕ 20 =? 0) then (
                3 + time_mem + 2 +
                if (99 =? xTask ⊕ 20) then (
                    time_branch + time_branch
                ) else (
                    3 + time_mem + if (99 =? xTask ⊕ 20) then (
                        time_branch + time_branch
                    ) else (
                        3 + time_mem + if (99 =? xTask ⊕ 20) then (
                            time_branch + time_branch
                        ) else (
                            3 + 2 + time_branch
                        )
                    )
                )
              ) else (
                time_branch + time_branch
              )
            ) else (
              time_branch + 2 + 2 +
              if (xTask ⊕ 20 =? gp ⊖ 1004) then (
                time_branch + time_branch
              ) else (
                if (xTask ⊕ 20 =? 0) then (
                  time_branch + time_branch
                ) else (
                  3 + 2 + time_branch
                )
              )
            )
          )
        )
      )
    ).

Definition eTaskGetState_timing_invs (s : store) (base_mem : addr -> N) (gp : N)
    (a3 : N) (xTask : addr) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000958 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_GP = Ⓓgp /\
                        s R_A0 = ⒹxTask /\
                        s R_A3 = Ⓓa3 /\
                        cycle_count_of_trace t' = 0)
| 0x800009e8 | 0x800009f0 => Some (time_of_eTaskGetState base_mem gp a3 xTask t)
| _ => None end | _ => None end.

Definition lifted_eTaskGetState : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem eTaskGetState_timing:
  forall s t s' x' base_mem gp a3 xTask
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (GP: s R_GP = Ⓓgp)
         (A0: s R_A0 = ⒹxTask)
         (A3: s R_A3 = Ⓓa3),
  satisfies_all 
    lifted_eTaskGetState
    (eTaskGetState_timing_invs s base_mem gp a3 xTask)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    destruct PRE as (MEM & GP & A0 & A3 & Cycles).
    repeat step.

    { unfold time_of_eTaskGetState, pxCurrentTCB.
        fold_big_subs. hammer. }

    unfold time_of_eTaskGetState, pxCurrentTCB.
        fold_big_subs. hammer.

    par:
        try solve [unfold time_of_eTaskGetState;
        unfold pxCurrentTCB; fold_big_subs;
        hammer].
