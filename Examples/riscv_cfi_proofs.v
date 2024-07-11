Require Import Picinae_riscv.
Require Import riscv_cfi.
Require Import riscvTiming.

Require Import List.
Import ListNotations.
Definition add_loop_riscv_offset : addr := 0x8%N.
Definition add_loop_riscv : list N := [
    0x00106393          	(* ori	t2,zero,1 *);
    0x000e7e13          	(* andi	t3,t3,0 *);
    0x01c28863         	    (* beq	t0,t3,20 <end> *);
    0x00130313          	(* addi	t1,t1,1 *);
    0x407282b3          	(* sub	t0,t0,t2 *);
    0xffce0ae3          	(* beq	t3,t3,10 <add> *)
]%N.
Definition add_loop_riscv_fun (_ : store) (a : addr) : N :=
    match a with
    | 0x8  => 0x00106393 (* ori     t2,zero,1 *)
    | 0xc  => 0x000e7e13 (* andi	t3,t3,0 *)
    | 0x10 => 0x01c28863 (* beq	t0,t3,20 <end> *)
    | 0x14 => 0x00130313 (* addi	t1,t1,1 *)
    | 0x18 => 0x407282b3 (* sub	t0,t0,t2 *)
    | 0x1c => 0xffce0ae3 (* beq	t3,t3,10 <add> *)
    | _ => 0 
    end.
Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (add_loop_riscv_fun s a) with
        | Some x => x | _ => 0 end.
End riscv_toa.

Module riscvT := MakeTimingContents riscvTiming riscv_toa.
Export riscvT.

Fixpoint _instruction_time_of_timed_program s (max_addr : nat) (p : timed_program) : nat :=
    match max_addr with 
    | O => match p s 0%N with None => 0 | Some (t, st) => t end
    | S n' => (match p s (N.of_nat max_addr) with | None => 0 | Some (t, st) => t end) +
        _instruction_time_of_timed_program s n' p
    end.

Definition instruction_time_of_timed_program s m p :=
    _instruction_time_of_timed_program s (N.to_nat m) p.

Definition range (base : N) (m : nat) : list N :=
    let fix aux max :=
        match max with
        | O => []
        | S n' =>
            let l := aux n' in
            base + N.of_nat (4 * List.length l) :: l
        end
    in List.rev (aux m).

Definition rv_stmt' m a :=
                                            (* removed getmem here. why was it giving nops? *)
  rv2il a match a mod 4 with 0 => rv_decode (m a) | _ => R5_InvalidI end.

Definition il_list : program_list :=
    List.map (fun a => (a, Some (4, rv_stmt' (add_loop_riscv_fun empty_store) a))) (range add_loop_riscv_offset (List.length add_loop_riscv)).

Definition lifted_addloop :=
    program_of_list il_list.

Definition common_inv (sum_cycles : N) (m : store) (a : addr) :=
    exists sum', sum' = sum_cycles + time_of_addr m a.
Hint Unfold common_inv : core.

Import RISCVNotations.
Definition postcondition (s : store) (x y : N) :=
    s R_T1 = Ⓓ(x ⊕ y).
Definition addloop_correctness_invs (_ : store) (p : addr) (x y : N) (t:trace) :=
    match t with (Addr a, s) :: _ => match a with
        | 0x8  => Some (s R_T0 = VaN x 32 /\ s R_T1 = VaN y 32)
        | 0x10 => Some (exists t0 t1, 
            s R_T0 = Ⓓt0 /\ s R_T1 = Ⓓt1 /\ s R_T2 = Ⓓ1 /\ s R_T3 = Ⓓ0 /\ 
                t0 ⊕ t1 = x ⊕ y)
        | 0x20 => Some (postcondition s x y)
        | _ => None end
    | _ => None
    end.

Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x20 => true
  | _ => false
  end | _ => false end.

Theorem addloop_welltyped: welltyped_prog rvtypctx lifted_addloop.
Proof. Picinae_typecheck. Qed.

Theorem addloop_partial_correctness:
  forall s p t s' x' a b
         (ENTRY: startof t (x',s') = (Addr 0x8,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = VaN a 32)                   (* Tie the contents of T0 to a *)
         (T1: s R_T1 = VaN b 32),                  (* Tie the contents of T1 to b *)
  satisfies_all 
    lifted_addloop                                 (* Provide lifted code *)
    (addloop_correctness_invs s p a b)             (* Provide invariant set *)
    addloop_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof.
    Local Ltac step := time rv_step.

    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. split.
        assumption.
        assumption.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply addloop_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Starting from our entrypoint at address 6, we'll do some setup and then
       step to the next invariant *)
    destruct PRE as [T0 T1]. step. step.
    (* This goal is the invariant at 0x10 and has taken us to the case in which
       the loop has just started *)
    (* A big mess, but most of this is solvable with reflexivity *)
    exists a, b. repeat split.
        assumption.
        assumption.

    (* We now have to deal with the cases where the loop terminates and where it
       loops around. Notice we get our invariant as an assumption! *)
    destruct PRE as [t0 [t1 [T0 [T1 [T2 [T3 Eq]]]]]].
    (* Termination case - time to prove the postcondition *)
    step.
        rewrite N.eqb_eq in BC. subst. psimpl in Eq.
        unfold postcondition. psimpl. rewrite <- Eq. assumption.
    (* Loop case - prove the invariant again *)
    step. step. step.
        rewrite N.eqb_neq in BC. exists (t0 ⊖ 1), (1 ⊕ t1). repeat split.
        psimpl. assumption.
Qed.

Definition cycle_count_of_trace (t : trace) : N :=
    List.fold_left N.add (List.map 
        (fun '(e, s) => match e with 
            | Addr a => time_of_addr s a
            | Raise n => max32
            end) t) 0.

Definition addloop_timing_invs (_ : store) (p : addr) (x y : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0x8  => Some (s R_T0 = Ⓓx /\ s R_T1 = Ⓓy /\ cycle_count_of_trace t = 2)
    | 0xc  => Some (s R_T0 = Ⓓx /\ s R_T2 = Ⓓ1 /\ cycle_count_of_trace t = 2 + 2)
    | 0x10 => Some (exists t0, s R_T0 = Ⓓt0 /\ s R_T2 = Ⓓ1 /\ s R_T3 = Ⓓ0 /\ t0 <= x /\
        cycle_count_of_trace t' = 2 + 2 + (x - t0) * (3 + 2 + 2 + (5 + (ML - 1))) /\ 
        cycle_count_of_trace [(Addr a, s)] = (if t0 =? 0 then 5 + (ML - 1) else 3))
    | 0x20 => Some (cycle_count_of_trace t = 2 + 2 + (5 + (ML - 1)) + x * (3 + 2 + 2 + (5 + (ML - 1))))
    | _ => None end
| _ => None
end.

Lemma fold_left_cons : forall {X : Type} (t : list X) (h : X) (f : X -> X -> X) (base : X) 
    (Comm : forall a b, f a b = f b a) (Assoc : forall a b c, f a (f b c) = f (f a b) c),
    List.fold_left f (h :: t) base = f h (List.fold_left f t base).
Proof.
    induction t; intros.
    - simpl. now rewrite Comm.
    - simpl in *. rewrite IHt, IHt, IHt,
        Assoc, Assoc, (Comm a h); auto.
Qed.

Lemma cycle_count_of_trace_single :
    forall (e : exit) (s : store),
    cycle_count_of_trace [(e, s)] = 
        match e with 
        | Addr a => time_of_addr s a
        | Raise n => max32
        end.
Proof. reflexivity. Qed.

Lemma cycle_count_of_trace_cons :
    forall (t : trace) (e : exit) (s : store),
    cycle_count_of_trace ((e, s) :: t) = cycle_count_of_trace [(e, s)] + cycle_count_of_trace t.
Proof.
    intros. unfold cycle_count_of_trace at 2. rewrite map_cons, fold_left_cons; try lia. simpl.
    unfold cycle_count_of_trace at 1. rewrite map_cons, fold_left_cons. rewrite N.add_0_r. reflexivity.
    lia. lia.
Qed.

Theorem addloop_timing:
  forall s p t s' x' a b
         (ENTRY: startof t (x',s') = (Addr 0x8,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = VaN a 32)                   (* Tie the contents of T0 to a *)
         (T1: s R_T1 = VaN b 32),                  (* Tie the contents of T1 to b *)
  satisfies_all 
    lifted_addloop                                 (* Provide lifted code *)
    (addloop_timing_invs s p a b)                  (* Provide invariant set *)
    addloop_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof.
    (* Local Ltac step := time rv_step. *)

    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. now repeat split.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply addloop_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Addr 0x8 *)
    destruct PRE as [T0 [T1 Cycles]].
    step. repeat split. assumption. rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single, Cycles. 
    unfold time_of_addr, add_loop_riscv_fun, neorv32_cycles_upper_bound, riscv_opcode, mask_bit_section.
    simpl (_ .& _). psimpl. unfold decompose_Itype, mask_bit_section. simpl (_ .& _). reflexivity.

    (* Addr 0xc *)
    destruct PRE as [T0 [T2 Cycles]].
    step. exists a. repeat split; try assumption. lia. psimpl. now rewrite Cycles.
    rewrite cycle_count_of_trace_single. unfold time_of_addr, add_loop_riscv_fun, neorv32_cycles_upper_bound,
        riscv_opcode, mask_bit_section. simpl (_ .& _). psimpl. unfold decompose_Btype, mask_bit_section.
    simpl (_ .& _). psimpl. now rewrite T0.

    (* Addr 0x10 *)
    destruct PRE as [t0 [T0 [T2 [T3 [T0_A [Cycles_t Cycles_16]]]]]]. psimpl in Cycles_t.
    step.
    - (* t0 = 0 -> postcondition *) 
        rewrite N.eqb_eq in BC; subst. repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single.
        unfold time_of_addr, neorv32_cycles_upper_bound. unfold add_loop_riscv_fun, riscv_opcode, mask_bit_section.
        simpl (_ .& _). simpl (_ =? _). psimpl. simpl (_ || _)%bool. psimpl.
        unfold decompose_Btype, mask_bit_section. simpl (_ .& _). psimpl. unfold rv_varid. rewrite T0, T3.
        rewrite N.eqb_refl. rewrite Cycles_t. psimpl. reflexivity.
    - (* t0 <> 0 -> loop again *)
        step. step. step. assert (1 <= t0) by (apply N.eqb_neq in BC; lia). exists (t0 ⊖ 1). repeat split.
        rewrite msub_nowrap. psimpl. lia. psimpl. assumption. psimpl.
        repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single.
        remember ((time_of_addr _) _). unfold time_of_addr, add_loop_riscv_fun, 
            neorv32_cycles_upper_bound, riscv_opcode, decompose_Btype, mask_bit_section in Heqn0. 
            simpl (_ .& _) in Heqn0. psimpl in Heqn0. unfold rv_varid in Heqn0. repeat psimpl in Heqn0.
        remember ((time_of_addr _) _). unfold time_of_addr, add_loop_riscv_fun, 
            neorv32_cycles_upper_bound, riscv_opcode, decompose_Rtype, mask_bit_section in Heqn1. 
            simpl (_ .& _) in Heqn1. psimpl in Heqn1.
        remember ((time_of_addr _) _). unfold time_of_addr, add_loop_riscv_fun, 
            neorv32_cycles_upper_bound, riscv_opcode, decompose_Btype, mask_bit_section in Heqn2.
            simpl (_ .& _) in Heqn2. psimpl in Heqn2. unfold rv_varid in Heqn2. rewrite T0, T3, BC in Heqn2.
        rewrite Cycles_t. subst. psimpl. rewrite N.add_sub_assoc; cycle 1. apply ML_pos.
         rewrite msub_nowrap; cycle 1. now psimpl.
        psimpl. rewrite N_sub_distr; cycle 1. assumption. assumption. psimpl. rewrite N.mul_add_distr_r. psimpl.
        rewrite (N.add_sub_assoc 16); cycle 1. apply ML_pos. psimpl. reflexivity.
Qed.
