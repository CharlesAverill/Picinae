Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

(* Common for all timing proofs - facilitates automation *)
Module vListInsertTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (RTOSDemo_NoAsserts_Clz a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x800023f0.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x80002428 => true
    | _ => false
  end | _ => false end.
End vListInsertTime.
Module vListInsertAuto := TimingAutomation vListInsertTime.
Import vListInsertTime vListInsertAuto.

(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L147 *)
Definition xItemValue (mem : addr -> N) (a : addr) : N :=
    mem Ⓓ[a].
Definition pxNext (mem : addr -> N) (a : addr) : addr :=
    mem Ⓓ[4 + a].
Definition portMAX_DELAY : N :=
    0 ⊖ 1.

(* Get the nth item of a linked list *)
Fixpoint linked_list_access (mem : addr -> N) (a : addr) (n : nat) : addr :=
    match n with
    | O => a
    | S n' => linked_list_access mem (pxNext mem a) n'
    end.

(* Postcondition *)
Definition time_of_vListInsert (t : trace) (base_mem : addr -> N) (a0 a1 : N) :=
    cycle_count_of_trace t =
        4 + time_mem.

Definition vListInsert_terminates (mem : addr -> N) 
    (pxList : addr) (pxNewListItem : addr) : Prop :=
    let xValueOfInsertion := xItemValue mem pxNewListItem in 
    xValueOfInsertion = portMAX_DELAY \/
    exists k, 
      xItemValue mem (linked_list_access mem pxList k) > xValueOfInsertion.

(* Invariants *)
(*
     Entrypoint       
          |           
          v           
  Degeneracy Check    
          |<---------+
          v          |
    Return Point     |
          |          |
          v          |
+--->Loop Start      |
|         |          |
|         v          |
+----Break Check     |
          |          |
          v          |
      Loop End-------+
*)
Definition vListInsert_timing_invs (base_mem : addr -> N) (a0 : N) (a1 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
(* Entrypoint *)
| 0x800023f0 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_A0 = Ⓓa0 /\ s R_A1 = Ⓓa1 /\
                      vListInsert_terminates base_mem a0 a1 /\
                        cycle_count_of_trace t' = 0)
(* Degeneracy Check *)
| 0x800023fc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
                        s R_A0 = Ⓓa0 /\ s R_A1 = Ⓓa1 /\
                        vListInsert_terminates mem a0 a1 /\
                        cycle_count_of_trace t' = 4 + time_mem)
(* Return Point *)
| 0x80002428 => Some (time_of_vListInsert t base_mem a0 a1)
(* Loop Start *)
| 0x8000242c => Some (exists k, cycle_count_of_trace t' = 
                        4 + time_mem + time_branch + 
                        k * (2 + 2 * time_mem + time_branch)
                     )
| _ => None end | _ => None end.

(* Lift the program *)
Definition lifted_vListInsert : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

Theorem vListInsert_timing:
  forall s t s' x' base_mem a0 a1
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓa0)
         (A1: s R_A1 = Ⓓa1)
         (TERMINATES: vListInsert_terminates base_mem a0 a1),
  satisfies_all 
    lifted_vListInsert
    (vListInsert_timing_invs base_mem a0 a1)
    exits
  ((x',s')::t).
Proof using.
    (* Specialize some automation tactics for our purposes *)
    Local Ltac step := time rv_step.

    (* Setup *)
    intros.
    apply prove_invs.
        simpl. rewrite ENTRY. unfold entry_addr. now step.

        intros.
        eapply startof_prefix in ENTRY; try eassumption.
        eapply preservation_exec_prog in MDL; 
            try eassumption; [idtac|apply lift_riscv_welltyped].
        clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    (* Proof start *)
    destruct_inv 32 PRE.

    (* Entrypoint *)
    destruct PRE as (MEM & A0 & A1 & TERMINATES & Cycles).
    repeat step.
    (* 0x800023fc *) {
        handle_ex. hammer. find_rewrites. unfold time_mem. lia.
    }

    destruct PRE as (mem & MEM & A0 & A1 & TERMINATES & Cycles).
    step.
    (* 0x8000242c - loop entry *) {
        exists 0. hammer. find_rewrites. unfold time_mem, time_branch.
        lia.
    }

    (* 0x80002428 - postcondition after degeneracy check fails *)
    admit.

    (* 0x8000242c - loop iterate *)
    repeat step.

    (* 0x80002428 - postcondition after loop exits *)
    admit.

    (* 0x8000242c - loop invariant after iteration *)
    destruct PRE as (k & Cycles).
    exists k. hammer. find_rewrites. apply Bool.negb_true_iff in BC.
    rewrite BC. psimpl. unfold time_mem, time_branch. psimpl. 

Qed.

