(* WIP : r5_step hangs *)

Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_uxQueueSpacesAvailable <: ProgramInformation.
    Definition entry_addr : N := 0x80003590.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800035b0 | 0x800029ac => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_uxQueueSpacesAvailable.

Module RISCVTiming := RISCVTiming cpu Program_uxQueueSpacesAvailable.
Module uxQueueSpacesAvailableAuto := RISCVTimingAutomation RISCVTiming.
Import Program_uxQueueSpacesAvailable uxQueueSpacesAvailableAuto.

(* Postcondition *)
Definition time_of_uxQueueSpacesAvailable (t : trace) (mem : memory) :=
    cycle_count_of_trace t =
        tcsrrci + tlw + tlw + tsub + tlui + tlw +
        if (mem Ⓓ[0x80080004] =? 0) then (
            tfbne + tcsrrsi
        ) else (
            ttbne
        ) + tjalr.

(* Invariants *)
Definition uxQueueSpacesAvailable_timing_invs (base_mem : memory)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80003590 => Some (s V_MEM32 = base_mem /\
            cycle_count_of_trace t' = 0)
| 0x800035b0 | 0x800029ac => Some (time_of_uxQueueSpacesAvailable t base_mem)
| _ => None end | _ => None end.

(*step through tactics in psimpl_in_hyp*)

Theorem uxQueueSpacesAvailable_timing:
  forall s t s' x' base_mem
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = base_mem),
  satisfies_all 
    lifted_prog
    (uxQueueSpacesAvailable_timing_invs base_mem)
    exits
  ((x',s')::t).
Proof using.
    (* Specialize some automation tactics for our purposes *)
    Local Ltac step := tstep r5_step.

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

    destruct PRE as (MEM & Cycles).
    do 6 step. (* psimpl hangs here *)
Abort.

End TimingProof.
