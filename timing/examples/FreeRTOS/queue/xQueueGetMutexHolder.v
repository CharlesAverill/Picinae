(* WIP : r5_step hanging *)

Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_xQueueGetMutexHolder <: ProgramInformation.
    Definition entry_addr : N := 0x8000296c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002994 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_xQueueGetMutexHolder.

Module RISCVTiming := RISCVTiming cpu Program_xQueueGetMutexHolder.
Module xQueueGetMutexHolderAuto := RISCVTimingAutomation RISCVTiming.
Import Program_xQueueGetMutexHolder xQueueGetMutexHolderAuto.

(* Postcondition *)
Definition time_of_xQueueGetMutexHolder (t : trace) (mem : memory) (xSemaphore : N):=
    cycle_count_of_trace t =
        taddi + tcsrrci + tlw + tlui + tlw + taddi +
        (if (mem Ⓓ[xSemaphore] =? 0) then (
            tfbne + tlw
        ) else ttbne) +
        (if (mem Ⓓ[0x80080004] =? 0) then (
            tfbne + tcsrrci
        ) else ttbne) +
        tjalr.

(* Invariants *)
Definition xQueueGetMutexHolder_timing_invs (base_mem : memory) (xSemaphore : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000296c => Some (s R_A0 = xSemaphore /\ s V_MEM32 = base_mem /\
            cycle_count_of_trace t' = 0)
| 0x80002984 => Some (s R_A5 = xSemaphore /\ s R_A3 = base_mem Ⓓ[xSemaphore] /\
            s R_A4 = base_mem Ⓓ[0x80080004] /\
            cycle_count_of_trace t' = taddi + tcsrrci + tlw + tlui +
                tlw + taddi)
| 0x80002994 => Some (time_of_xQueueGetMutexHolder t base_mem xSemaphore)
| _ => None end | _ => None end.

Theorem xQueueGetMutexHolder_timing:
  forall s t s' x' base_mem xSemaphore
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = xSemaphore),
  satisfies_all 
    lifted_prog
    (xQueueGetMutexHolder_timing_invs base_mem xSemaphore)
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

    destruct PRE as (SEM & MEM & Cycles).
    repeat step. repeat split.
    hammer.

    destruct PRE as (A5 & A3 & A4 & Cycles).
    step.
        admit. (* r5_step hangs here? *)
    step.
        admit. (* r5_step hangs here too *)
Abort.

End TimingProof.
