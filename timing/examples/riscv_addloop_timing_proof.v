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
Definition sum (low high : N) (f : N -> N) : N :=
    let range := List.map N.of_nat (List.seq (N.to_nat low) (N.to_nat (high - low))) in
    List.fold_left (fun acc i => acc + f i) range 0.

Lemma sum_0_0 : forall f, sum 0 0 f = 0.
Proof. reflexivity. Qed.

Lemma sum_Sn : forall low high f,
    low <= high ->
    sum low (1 + high) f = sum low high f + f high.
Proof.
    intros. unfold sum at 1.
    rewrite <- N.add_sub_assoc, N.add_1_l, N2Nat.inj_succ.
    rewrite seq_S, map_app, fold_left_app. simpl.
    rewrite N2Nat.inj_sub at 2.
    rewrite Arith_base.le_plus_minus_r_stt by lia.
    rewrite N2Nat.id. reflexivity. assumption.
Qed.

Lemma sum_sub1 : forall low high body,
    low < high ->
    sum low (high - 1) (fun _ => body) + body = 
        sum low high (fun _ => body).
Proof.
    intros. unfold sum at 2.
    destruct (high - low) eqn:E using N.peano_ind.
    - lia.
    - clear IHn. rewrite N2Nat.inj_succ, seq_S, map_app, fold_left_app.
      simpl. unfold sum. now replace n with (high - 1 - low) by lia.
Qed.

Definition addloop_timing_invs (t3 x y : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0x8  => Some (s R_T0 = x /\ s R_T1 = y /\ s R_T3 = t3 /\
        cycle_count_of_trace t' = 0)
    | 0x10 => Some (s R_T2 = 1 /\ s R_T3 = 0 /\
        s R_T0 <= x /\ s R_T1 = y ⊕ (x - s R_T0) /\
        cycle_count_of_trace t' = 
            (tori 0 1) + (tandi t3 0) + 
            sum 0 (x - s R_T0) (fun i =>
                tfbeq (x - i) 0 +
                taddi (y ⊕ i) 1 +
                tsub (x - i) 1 +
                ttbeq 0 0
            ))
    | 0x20 => Some (cycle_count_of_trace t' = 
            (tori 0 1) + (tandi t3 0) + 
            sum 0 x (fun i =>
                tfbeq (x - i) 0 +
                taddi (y ⊕ i) 1 +
                tsub (x - i) 1 +
                ttbeq 0 0
            ) + ttbeq 0 0)
        (* 2 + 2 + (5 + (ML - 1)) + x * (3 + 2 + 2 + (5 + (ML - 1))) *)
    | _ => None end
| _ => None
end.

Theorem addloop_timing:
  forall s t s' x' x y t3
         (ENTRY: startof t (x',s') = (Addr entry_addr,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = x)                   (* Tie the contents of T0 to x *)
         (T1: s R_T1 = y)                  (* Tie the contents of T1 to y *)
         (T3: s R_T3 = t3),
  satisfies_all 
    lifted_prog                                 (* Provide lifted code *)
    (addloop_timing_invs t3 x y)                  (* Provide invariant set *)
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
    destruct PRE as [T0 [T2 [T3 Cycles]]].
    repeat step. repeat split; try assumption. lia.
    subst. rewrite N.sub_diag, N.add_0_r.
        now rewrite N.mod_small by apply (models_var R_T1 MDL).
    hammer. rewrite N.sub_diag, sum_0_0. lia.

    (* Addr 0x10 *)
    destruct PRE as [T2 [T3 [T0 [T1 Cycles_t]]]].
    step.
    - (* t0 = 0 -> postcondition *)
        remember (sum 0 x _).
        hammer. apply N.eqb_eq in BC. rewrite BC, N.sub_0_r.
        subst n. lia.
    - (* t0 <> 0 -> loop again *)
        step. step. step.
        rewrite msub_nowrap by (psimpl; lia).
        repeat split; try lia;
            rewrite (N.mod_small (s' R_T0)) by
                apply (models_var R_T0 MDL);
            rewrite (N.mod_small 1) by lia.
            rewrite N_sub_distr; lia.
        remember (sum 0 (x - update _ _ _ _) _).
        hammer. subst n. rewrite update_updated.
        rewrite N_sub_distr, (N.add_comm _ 1), sum_Sn,
            N_sub_distr, N.sub_diag, N.add_0_l;
            auto; try lia. 
Qed.

End TimingProof.
