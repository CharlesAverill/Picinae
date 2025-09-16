Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_vListInitialiseItem <: ProgramInformation.
    Definition entry_addr : N := 0x800023bc.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800023c0 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vListInitialiseItem.

Module RISCVTiming := RISCVTiming cpu Program_vListInitialiseItem.
Module vListInitialiseItemAuto := RISCVTimingAutomation RISCVTiming.
Import Program_vListInitialiseItem vListInitialiseItemAuto.

(* Postcondition *)
Definition time_of_vListInitialiseItem (t : trace) :=
    cycle_count_of_trace t = tsw + tjalr.

(* Invariants *)
Definition vListInitialiseItem_timing_invs (base_mem : memory) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023bc => Some (cycle_count_of_trace t' = 0)
| 0x800023c0 => Some (time_of_vListInitialiseItem t)
| _ => None end | _ => None end.

Theorem vListInitialiseItem_timing:
  forall s t s' x' base_mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_prog
    (vListInitialiseItem_timing_invs base_mem a0)
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

    repeat step. hammer.
Qed.

End TimingProof.
