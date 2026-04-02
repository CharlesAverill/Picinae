Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_uxListRemove <: ProgramInformation.
    Definition entry_addr : N := 0x80002440.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002470 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_uxListRemove.

Module RISCVTiming := RISCVTiming cpu Program_uxListRemove.
Module uxListRemoveAuto := RISCVTimingAutomation RISCVTiming.
Import Program_uxListRemove uxListRemoveAuto.

(* Postcondition *)
Definition time_of_uxListRemove (t : trace) (mem : memory) (a0 : N) :=
    cycle_count_of_trace t =
        tlw + tlw + tlw + tsw + tsw + tlw +
        (if mem Ⓓ[4 + mem Ⓓ[16 + a0]] =? a0 then
            tfbne + tsw 
         else
            ttbne) +
        tsw + tlw + taddi + tsw + tjalr.

(* These values are used frequently, so we give them names for readability *)
(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L143 *)
Definition xItemValue (mem : memory) (list_item_addr : addr) : N :=
    mem Ⓓ[list_item_addr].
Definition pxNext (mem : memory) (list_item_addr : addr) : addr :=
    mem Ⓓ[4 + list_item_addr].
Definition pxPrevious (mem : memory) (list_item_addr : addr) : addr :=
    mem Ⓓ[8 + list_item_addr].
Definition pxContainer (mem : memory) (list_item_addr : addr) : addr :=
    mem Ⓓ[16 + list_item_addr].
(* https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/include/list.h#L176 *)
Definition pxIndex (mem : memory) (list_addr : addr) : N :=
    mem Ⓓ[4 + list_addr].

(* Declare which regions of memory should not overlap. The `map` call just 
   helps state that each address is for a buffer of length 4
*)
Definition memory_regions (mem : memory) (a0 : N) := 
    [(4, 4 + a0); (4, 8 + a0); (4, 16 + a0);
     (4, 4 + (pxPrevious mem a0)); (4, 8 + (pxNext mem a0));
     (4, 4 + (pxContainer mem a0))].

Definition noverlaps (mem : memory) (a0 : N) :=
    create_noverlaps (memory_regions mem a0).

(* Invariants *)
Definition uxListRemove_timing_invs (base_mem : memory) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002440 => Some (s R_A0 = a0 /\ s V_MEM32 = base_mem /\
                        noverlaps base_mem a0 /\
                        cycle_count_of_trace t' = 0)
| 0x80002460 => Some (noverlaps (s V_MEM32) a0 /\
                        cycle_count_of_trace t' = 
                            tlw + tlw + tlw + tsw + tsw + tlw +
                            (if base_mem Ⓓ[4 + base_mem Ⓓ[16 + a0]] =? a0 then 
                                tfbne + tsw 
                            else
                                ttbne))
| 0x80002470 => Some (time_of_uxListRemove t base_mem a0)
| _ => None end | _ => None end.

Theorem uxListRemove_timing:
  forall s t s' x' base_mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (NVL : create_noverlaps (memory_regions base_mem a0))
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = a0),
  satisfies_all 
    lifted_prog
    (uxListRemove_timing_invs base_mem a0)
    exits
  ((x',s')::t).
Proof using.
    (* Specialize some automation tactics for our purposes *)
    Local Ltac step := tstep r5_step.
    Local Ltac unfold_noverlap :=
        unfold noverlaps, memory_regions,
            pxNext, pxPrevious, pxContainer, pxIndex in *.
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
        split.
            preserve_noverlaps.
            hammer.
        unfold_noverlap. unfold_create_noverlaps.
        rewrite getmem_noverlap, getmem_noverlap in BC by 
            (auto using noverlap_symmetry).
        find_rewrites. lia.
    }
    (* Invariant 0x80002460 when branch isn't taken *) {
        split.
            preserve_noverlaps.
            hammer.
        unfold_noverlap. unfold_create_noverlaps.
        rewrite getmem_noverlap, getmem_noverlap in BC by
            (auto using noverlap_symmetry).
        find_rewrites. lia.
    }

    (* Postcondition - `repeat step` got us here (repeat is weird) *)
    destruct PRE as (NVL & Cycles).
    repeat step. hammer.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall t m item,
    time_of_uxListRemove t m item = 
    (uxListRemoveAuto.cycle_count_of_trace t =
        19 +
        (if pxIndex m (pxContainer m item) =? item
        then 31 + 7 * T_data_latency
        else 29 + 6 * T_data_latency + T_inst_latency) + 
        3 * T_data_latency + T_inst_latency).
Proof.
    intros. unfold time_of_uxListRemove.
    unfold tlw, tsw, tfbne, ttbne, taddi, tjalr, pxIndex, pxContainer.
    psimpl. repeat rewrite <- N.add_assoc.
    replace (T_data_latency + _) with (7 * T_data_latency) by lia.
    replace (T_data_latency + _) with (6 * T_data_latency + T_inst_latency) by lia.
    replace (T_data_latency + _) with (3 * T_data_latency + T_inst_latency) by lia.
    destruct (m Ⓓ[ 4 + m Ⓓ[ 16 + item ] ]), item.
    all: psimpl; now psimpl.
Qed.
