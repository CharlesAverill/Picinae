(* See Examples/riscv_addloop_proof.v for explanations of non-timing stuff *)

Require Import array.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import ZifyBool.

(* Each timing proof is a module that takes as input a description
   of a CPU's timing behavior. This makes it so that one timing proof
   can be used for any CPU running the target program. In other words,
   timing proofs are CPU-agnostic and ISA-specific.
*)
Module TimingProof (cpu : CPUTimingBehavior).

(* ProgramInformation modules are used as inputs to the TimingAutomation 
   module, which (you guessed it) provides automation for timing proofs
*)
Module Program_addloop <: ProgramInformation.
    Definition entry_addr : N := 0x8.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x20 => true
        | _ => false
    end | _ => false end.

    Definition binary (a : addr) : N :=
        match a with
        | 0x8  => 0x00106393 (* ori     t2,zero,1 *)
        | 0xc  => 0x000e7e13 (* andi	t3,t3,0 *)
        | 0x10 => 0x01c28863 (* beq	t0,t3,20 <end> *)
        | 0x14 => 0x00130313 (* addi	t1,t1,1 *)
        | 0x18 => 0x407282b3 (* sub	t0,t0,t2 *)
        | 0x1c => 0xffce0ae3 (* beq	t3,t3,10 <add> *)
        | _ => 0 
        end.
End Program_addloop.

(* Build the timing module and automation module and import them *)
Module RISCVTiming := RISCVTiming cpu Program_addloop.
Module addloopAuto := RISCVTimingAutomation RISCVTiming.
Import Program_addloop addloopAuto.

(* Now we define invariants. These are in the same format as Picinae
   correctness invariants, however the primary goal in each invariant is now
   "cycle_count_of_trace t' = ..."

   We choose t' to reason about because this gets us out of having to put
   unnecessary branches in our timing expressions should they appear. For example,
   if you have a branch that could either lead to continuing through the program
   on one side and lead to an infinite loop on the other (such that no timing 
   expression can be written), it's more convenient to not include that branch in
   the timing expression, and we don't lose any soundness

   Because timing proofs are CPU-agnostic, we write our timing expressions in
   terms of abstract instruction timing values. For example, even though the
   "addi" instruction on one CPU may take 2 cycles, the proof will refer to
   the time of addi as "taddi". taddi is a value instantiated in a
   CPUTimingBehavior module for each supported CPU.

   For branch instructions, we have times for taken branches and non-taken
   branches. They may be the same on some CPUs, but we must account for the fact
   that they might be different. For example, if the "beq" instruction is taken,
   its time is "ttbeq". But if it falls through, its time is "tfbeq".
   We see this behavior in the invariant set below, because in the loop body,
   the loop condition *must* have fallen through. But after the loop exits,
   we know that the loop condition must have taken the branch.
*)
Definition addloop_timing_invs (x y : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0x8  => Some (s R_T0 = x /\ s R_T1 = y /\
        cycle_count_of_trace t' = 0)
    | 0x10 => Some (s R_T2 = 1 /\ s R_T3 = 0 /\ 
        s R_T0 <= x /\
        cycle_count_of_trace t' = 
            tori + tandi + (x - s R_T0) * (tfbeq + taddi + tsub + ttbeq))
        (* 2 + 2 + (x - t0) * (3 + 2 + 2 + (5 + (ML - 1)) *)
    | 0x20 => Some (cycle_count_of_trace t' = 
            tori + tandi + x * (tfbeq + taddi + tsub + ttbeq) + ttbeq)
        (* 2 + 2 + (5 + (ML - 1)) + x * (3 + 2 + 2 + (5 + (ML - 1))) *)
    | _ => None end
| _ => None
end.

Theorem addloop_timing:
  forall s t s' x' x y
         (ENTRY: startof t (x',s') = (Addr entry_addr,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = x)                   (* Tie the contents of T0 to x *)
         (T1: s R_T1 = y),                  (* Tie the contents of T1 to y *)
  satisfies_all 
    lifted_prog                                 (* Provide lifted code *)
    (addloop_timing_invs x y)                  (* Provide invariant set *)
    exits                                   (* Provide exit point *)
  ((x',s')::t).
Proof.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    (* Base case *)
    simpl. rewrite ENTRY. step.
    split.
        assumption.
    split.
        assumption.
    hammer.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Addr 0x8 *)
    destruct PRE as [T0 [T2 Cycles]].
    repeat step. repeat split; try assumption. lia. 
    hammer.

    (* Addr 0x10 *)
    destruct PRE as [T2 [T3 [T0 Cycles_t]]].
    step.
    - (* t0 = 0 -> postcondition *)
        hammer.
    - (* t0 <> 0 -> loop again *)
        step. step. step.
        rewrite msub_nowrap by (psimpl; lia).
        repeat split.
            lia.
        hammer. rewrite N_sub_distr; lia.
Qed.

End TimingProof.
