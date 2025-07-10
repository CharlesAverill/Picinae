(* Problem with this function - it contains what is essentially a strcmp, I don't
   want to deal with the break in the middle of it right now *)

Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module prvSearchForNameWithinSingleListTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x80000114.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x80000130 | 0x80000168 => true
    | _ => false
  end | _ => false end.
End prvSearchForNameWithinSingleListTime.

Module prvSearchForNameWithinSingleListAuto := TimingAutomation prvSearchForNameWithinSingleListTime.
Import prvSearchForNameWithinSingleListTime prvSearchForNameWithinSingleListAuto.

Definition pvOwner (mem : addr -> N) (a : addr) : addr :=
    mem Ⓓ[12 + a].
Definition pxNext (mem : addr -> N) (a : addr) : addr :=
    mem Ⓓ[8 + a].
(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L172 *)
Definition uxNumberOfItems (mem : addr -> N) (a : addr) : N :=
    mem Ⓓ[a].
Definition xListEnd (mem : addr -> N) (a : addr) : addr :=
    mem Ⓓ[8 + a].
(* I think this is due to the compiler flattening the List_t and MiniListItem_t structs *)
Definition listGET_HEAD_ENTRY (mem : addr -> N) (a : addr) : addr :=
    mem Ⓓ[12 + a].
Definition pcTaskName (mem : addr -> N) (a : addr) : addr :=
    mem Ⓑ[52 + a].

Fixpoint linked_list_length (mem : addr -> N) (list item : addr) (max : nat) : N :=
    match max with
    | O => 0
    | S max' => 
        if item =? xListEnd mem list then
            0
        else
            1 + linked_list_length mem list (pxNext mem item) max'
    end.

Definition time_of_prvSearchForNameWithinSingleList (t : trace) 
      (mem : addr -> N) (pxList pcNameToQuery : addr) (match_idx : option N) :=
  cycle_count_of_trace t = time_mem +
    (if negb (uxNumberOfItems mem pxList =? 0) then (
      3 + time_mem + 2 + 2 +
      (match match_idx with 
      | None => linked_list_length mem pxList (listGET_HEAD_ENTRY mem pxList) (Nat.pow 2 32)
      | Some idx => idx
      end) (* number of loop iterations *) *
      (if listGET_HEAD_ENTRY mem pxList =? 8 ⊕ pxList (* &(pxList->xListEnd) *) then
         3 + 2 + time_branch
       else (
         time_mem + 2 + 2 + time_mem + 2 + time_mem + 3)
      ) (* loop body duration *)
    )
    else (
      time_branch + 2 + time_branch
    )).

Definition prvSearchForNameWithinSingleList_timing_invs 
    (base_mem : addr -> N) (a0 a1 : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000114 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_A0 = Ⓓa0 /\ s R_A1 = Ⓓa1 /\
                        cycle_count_of_trace t' = 0)
| 0x80000130 | 0x80000168 => Some (time_of_prvSearchForNameWithinSingleList t base_mem a0)
| _ => None end | _ => None end.

Definition lifted_prvSearchForNameWithinSingleList : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem prvSearchForNameWithinSingleList_timing:
  forall s t s' x' base_mem a0 a1
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓa0)
         (A1: s R_A1 = Ⓓa1),
  satisfies_all 
    lifted_prvSearchForNameWithinSingleList
    (prvSearchForNameWithinSingleList_timing_invs base_mem a0 a1)
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

    destruct PRE as (MEM & A0 & Cycles).
    step. step. (* 0x80000118: beqz a5,8000012c *)
    - (* m[a0] = 0, postcondition *)
      repeat step. unfold time_of_prvSearchForNameWithinSingleList, uxNumberOfItems, listGET_HEAD_ENTRY.
      hammer. find_rewrites. unfold time_mem, time_branch. lia.
    - (* m[a0] != 0 *)
      step. step. step. step. (* 0x80000128: bne a4,a2,80000134 *)
      -- (* m [12 + a0] != 8 + n *)
          step. step. step. step. step. step. step.
      -- (* m [12 + a0] = 8 + n *)
          step. (* postcondition *)
          unfold time_of_prvSearchForNameWithinSingleList, uxNumberOfItems, listGET_HEAD_ENTRY.
          hammer. change ((8 + a0) mod 4294967296) with (8 ⊕ a0). find_rewrites.
          psimpl. cbn [negb]. unfold time_mem, time_branch. apply Bool.negb_false_iff in BC0.
          rewrite BC0. lia.
Qed.

