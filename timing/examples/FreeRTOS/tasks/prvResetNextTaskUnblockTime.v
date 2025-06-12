Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Definition time_mem : N :=
    5 + (ML - 2).
Definition time_branch : N :=
    5 + (ML - 1).

Module prvResetNextTaskUnblockTimeTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x80000478.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x8000048c => true
    | _ => false
  end | _ => false end.
End prvResetNextTaskUnblockTimeTime.

Module prvResetNextTaskUnblockTimeAuto := TimingAutomation prvResetNextTaskUnblockTimeTime.
Import prvResetNextTaskUnblockTimeTime prvResetNextTaskUnblockTimeAuto.

Definition time_of_prvResetNextTaskUnblockTime (mem : addr -> N) (gp : N) (t : trace) :=
    cycle_count_of_trace t = 2 * time_mem +
        (if mem Ⓓ[mem Ⓓ[(0 ⊖ 1900) + gp]] =? 0 then 
            3 + 2
         else
            time_branch + 3 * time_mem + time_branch) +
        time_mem + time_branch.

Definition prvResetNextTaskUnblockTime_timing_invs (s : store) (base_mem : addr -> N) (gp : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000478 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_GP = Ⓓgp /\ cycle_count_of_trace t' = 0)
| 0x8000048c => Some (time_of_prvResetNextTaskUnblockTime base_mem gp t)
| _ => None end | _ => None end.

Definition lifted_prvResetNextTaskUnblockTime : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem prvResetNextTaskUnblockTime_timing:
  forall s t s' x' base_mem gp
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (GP: s R_GP = Ⓓgp),
  satisfies_all 
    lifted_prvResetNextTaskUnblockTime
    (prvResetNextTaskUnblockTime_timing_invs s base_mem gp)
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

    destruct PRE as (MEM & GP & Cycles).
    repeat step.
    unfold time_of_prvResetNextTaskUnblockTime.
        hammer. find_rewrites.
        unfold time_mem, time_branch. lia.
    unfold time_of_prvResetNextTaskUnblockTime.
        hammer. find_rewrites.
        unfold time_mem, time_branch. lia. 
Qed.

