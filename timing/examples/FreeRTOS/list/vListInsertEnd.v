Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_vListInsertEnd <: ProgramInformation.
    Definition entry_addr : N := 0x800023c4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800023ec => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vListInsertEnd.

Module RISCVTiming := RISCVTiming cpu Program_vListInsertEnd.
Module vListInsertEndAuto := RISCVTimingAutomation RISCVTiming.
Import Program_vListInsertEnd vListInsertEndAuto.

(* Postcondition *)
Definition time_of_vListInsertEnd (t : trace) :=
    cycle_count_of_trace t =
        tlw + tlw + tsw + tsw + tsw + tsw + tlw + tsw +
        taddi + tsw + tjalr.

(* Invariants *)
Definition vListInsertEnd_timing_invs (base_mem : memory) (a0 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023c4 => Some (cycle_count_of_trace t' = 0)
| 0x800023ec => Some (time_of_vListInsertEnd t)
| _ => None end | _ => None end.

Theorem vListInsertEnd_timing:
  forall s t s' x' base_mem a0
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_prog
    (vListInsertEnd_timing_invs base_mem a0)
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

Compute (lifted_prog (fun _ => 0) 0x80002970).

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall t,
    time_of_vListInsertEnd t = 
    (vListInsertEndAuto.cycle_count_of_trace t =
        43 + 9 * T_data_latency + T_inst_latency).
Proof.
    intros. unfold time_of_vListInsertEnd.
    unfold taddi, tlw, tsw, tjalr. psimpl.
    repeat rewrite <- N.add_assoc.
    now replace (T_data_latency + _) with (9 * T_data_latency + T_inst_latency) by lia.
Qed.
