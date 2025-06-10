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

Module uxListRemoveTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x80002440.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x80002470 => true
    | _ => false
  end | _ => false end.
End uxListRemoveTime.

Module uxListRemoveAuto := TimingAutomation uxListRemoveTime.
Import uxListRemoveTime uxListRemoveAuto.

Definition time_of_uxListRemove (t : trace) (base_mem : addr -> N) (a0 : N) :=
    cycle_count_of_trace t = 6 * time_mem +
        (if base_mem Ⓓ[4 + base_mem Ⓓ[16 + a0]] =? a0 then 3 + time_mem else time_branch) + 
        3 * time_mem + 2 + time_branch.

(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L143 *)
Definition xItemValue (mem : addr -> N) (list_item_addr : addr) : N :=
    mem Ⓓ[list_item_addr].
Definition pxNext (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[4 + list_item_addr].
Definition pxPrevious (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[8 + list_item_addr].
Definition pxContainer (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[16 + list_item_addr].

Definition pxIndex (mem : addr -> N) (list_addr : addr) : N :=
    mem Ⓓ[4 + list_addr].

Definition noverlaps (mem : addr -> N) (a0 : N) :=
    let regions := map (fun x => (4, x)) 
        [4 + a0; 8 + a0; 16 + a0;
         4 + (pxPrevious mem a0); 8 + (pxNext mem a0);
         4 + (pxContainer mem a0)] in
    create_noverlaps regions regions.

Definition uxListRemove_timing_invs (base_mem : addr -> N) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002440 => Some (s R_A0 = Ⓓa0 /\ s V_MEM32 = Ⓜbase_mem /\
                        noverlaps base_mem a0 /\
                        cycle_count_of_trace t' = 0)
| 0x80002460 => Some (exists mem, s V_MEM32 = Ⓜmem /\
                        noverlaps mem a0 /\
                        cycle_count_of_trace t' = 6 * time_mem +
                            (if base_mem Ⓓ[4 + base_mem Ⓓ[16 + a0]] =? a0 then 3 + time_mem else time_branch))
| 0x80002470 => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
                        time_of_uxListRemove t base_mem a0)
| _ => None end | _ => None end.

Definition lifted_uxListRemove : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem uxListRemove_timing:
  forall s t s' x' base_mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (NVL : noverlaps base_mem a0)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓa0),
  satisfies_all 
    lifted_uxListRemove
    (uxListRemove_timing_invs base_mem a0)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.
    Local Ltac unfold_noverlap :=
        unfold pxNext, pxPrevious, pxContainer, pxIndex, noverlaps in *.
    Local Ltac preserve_noverlaps := 
        noverlaps_preserved unfold_noverlap.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (cycles & A0 & NVL & MEM).
    repeat step. {
        eexists. split. reflexivity. split.
            preserve_noverlaps.
        hammer. find_rewrites. unfold_create_noverlaps unfold_noverlap.
        rewrite getmem_noverlap, getmem_noverlap in BC by auto.
        apply Bool.negb_true_iff in BC. rewrite BC. unfold time_mem, time_branch.
        psimpl. lia.
    } {
        eexists. split. reflexivity. split.
            preserve_noverlaps.
        hammer. find_rewrites. unfold_create_noverlaps unfold_noverlap.
        rewrite getmem_noverlap, getmem_noverlap in BC by auto.
        apply Bool.negb_false_iff in BC. rewrite BC. unfold time_mem, time_branch.
        psimpl. lia.
    }

    destruct PRE as (mem & MEM & NVL & Cycles).
    repeat step. eexists. split. reflexivity.
    unfold time_of_uxListRemove. hammer. find_rewrites. psimpl.
    unfold time_mem, time_branch. psimpl. destruct N.eqb; psimpl; lia.
Qed.

