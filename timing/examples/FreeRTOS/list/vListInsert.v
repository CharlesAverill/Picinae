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
Module vListInsertTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
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

(* Postcondition *)
Definition time_of_vListInsert (t : trace) (base_mem : addr -> N) (a0 : N) :=
    True.

(* Invariants *)
Definition vListInsert_timing_invs (base_mem : addr -> N) (a0 : N) (a1 : N)
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023f0 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_A0 = Ⓓa0 /\ s R_A1 = Ⓓa1 /\
                        cycle_count_of_trace t' = 0)
| 0x800023fc => Some (exists mem, s V_MEM32 = Ⓜmem /\ 
                        s R_A0 = Ⓓa0 /\ s R_A1 = Ⓓa1 /\
                        cycle_count_of_trace t' = 4 + time_mem)
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
         (A1: s R_A1 = Ⓓa1),
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
    destruct PRE as (MEM & A0 & A1 & Cycles).
    repeat step.
    (* 0x800023fc *)
    handle_ex. hammer. find_rewrites. unfold time_mem. lia.
Admitted.

