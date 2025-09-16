Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_xQueueGetMutexHolderFromISR <: ProgramInformation.
    Definition entry_addr : N := 0x80002998.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800029a4 | 0x800029ac => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_xQueueGetMutexHolderFromISR.

Module RISCVTiming := RISCVTiming cpu Program_xQueueGetMutexHolderFromISR.
Module xQueueGetMutexHolderFromISRAuto := RISCVTimingAutomation RISCVTiming.
Import Program_xQueueGetMutexHolderFromISR xQueueGetMutexHolderFromISRAuto.

(* Postcondition *)
Definition time_of_xQueueGetMutexHolderFromISR (t : trace) (mem : memory) (xSemaphore : N):=
    cycle_count_of_trace t =
        tlw +
        if (mem Ⓓ[xSemaphore] =? 0) then (
            tfbne + tlw + tjalr
        ) else (
            ttbne + taddi + tjalr
        ).

(* Invariants *)
Definition xQueueGetMutexHolderFromISR_timing_invs (base_mem : memory) (xSemaphore : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002998 => Some (s R_A0 = xSemaphore /\ s V_MEM32 = base_mem /\
            cycle_count_of_trace t' = 0)
| 0x800029a4 | 0x800029ac => Some (time_of_xQueueGetMutexHolderFromISR t base_mem xSemaphore)
| _ => None end | _ => None end.

Theorem xQueueGetMutexHolderFromISR_timing:
  forall s t s' x' base_mem xSemaphore
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = xSemaphore),
  satisfies_all 
    lifted_prog
    (xQueueGetMutexHolderFromISR_timing_invs base_mem xSemaphore)
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
    repeat step; hammer.
Qed.

End TimingProof.
