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

(* Common for all timing proofs - facilitates automation *)
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

(* Postcondition *)
Definition time_of_uxListRemove (t : trace) (base_mem : addr -> N) (a0 : N) :=
    cycle_count_of_trace t = 6 * time_mem +
        (if base_mem Ⓓ[4 + base_mem Ⓓ[16 + a0]] =? a0 then 3 + time_mem else time_branch) + 
        3 * time_mem + 2 + time_branch.

(* These values are used frequently, so we give them names for readability *)
(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L143 *)
Definition xItemValue (mem : addr -> N) (list_item_addr : addr) : N :=
    mem Ⓓ[list_item_addr].
Definition pxNext (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[4 + list_item_addr].
Definition pxPrevious (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[8 + list_item_addr].
Definition pxContainer (mem : addr -> N) (list_item_addr : addr) : addr :=
    mem Ⓓ[16 + list_item_addr].
(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L176 *)
Definition pxIndex (mem : addr -> N) (list_addr : addr) : N :=
    mem Ⓓ[4 + list_addr].

(* Declare which regions of memory should not overlap. The `map` call just 
   helps state that each address is for a buffer of length 4
*)
Definition memory_regions (mem : addr -> N) (a0 : N) := 
    map (fun x => (4, x)) 
        [4 + a0; 8 + a0; 16 + a0;
        4 + (pxPrevious mem a0); 8 + (pxNext mem a0);
        4 + (pxContainer mem a0)].

Definition noverlaps (mem : addr -> N) (a0 : N) :=
    create_noverlaps (memory_regions mem a0).

(* Invariants *)
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

(* Lift the program *)
Definition lifted_uxListRemove : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.

Theorem uxListRemove_timing:
  forall s t s' x' base_mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (NVL : create_noverlaps (memory_regions base_mem a0))
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓa0),
  satisfies_all 
    lifted_uxListRemove
    (uxListRemove_timing_invs base_mem a0)
    exits
  ((x',s')::t).
Proof using.
    (* Specialize some automation tactics for our purposes *)
    Local Ltac step := time rv_step.
    Local Ltac unfold_noverlap :=
        unfold pxNext, pxPrevious, pxContainer, pxIndex, 
            memory_regions, noverlaps in *.
    Local Ltac preserve_noverlaps := 
        noverlaps_preserved unfold_noverlap.

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
    destruct PRE as (cycles & A0 & NVL & MEM).
    repeat step. 
    (* Invariant 0x80002460 when branch is taken *) {
        eexists. split. reflexivity. split.
            preserve_noverlaps.
        hammer. find_rewrites. unfold_create_noverlaps unfold_noverlap.
        rewrite getmem_noverlap, getmem_noverlap in BC by auto using noverlap_symmetry.
        find_rewrites. unfold time_mem, time_branch. lia.
    }
    (* Invariant 0x80002460 when branch isn't taken *) {
        eexists. split. reflexivity. split.
            preserve_noverlaps.
        hammer. find_rewrites. unfold_create_noverlaps unfold_noverlap.
        rewrite getmem_noverlap, getmem_noverlap in BC by auto using noverlap_symmetry.
        find_rewrites. unfold time_mem, time_branch. lia.
    }

    (* Postcondition - `repeat step` got us here (repeat is weird) *)
    destruct PRE as (mem & MEM & NVL & Cycles).
    repeat step. eexists. split. reflexivity.
    unfold time_of_uxListRemove. hammer. find_rewrites.
    unfold time_mem, time_branch. lia.
Qed.

