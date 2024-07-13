Require Import Picinae_riscv.
Require Import riscv_cfi.
Require Import riscvTiming.
Require Import List.
Import RISCVNotations.
Import ListNotations.

Definition add_loop_riscv_offset : addr := 0x8%N.
Definition add_loop_riscv : list N := [
    0x00106393          	(* ori	t2,zero,1 *);           (* 2 cycles *)
    0x000e7e13          	(* andi	t3,t3,0 *);             (* 2 cycles *)
    0x01c28863         	    (* beq	t0,t3,20 <end> *);      (* if taken then 5 + (ML - 1) else 3 *)
    0x00130313          	(* addi	t1,t1,1 *);             (* 2 cycles *)
    0x407282b3          	(* sub	t0,t0,t2 *);            (* 2 cycles *)
    0xffce0ae3          	(* beq	t3,t3,10 <add> *)       (* 5 + (ML - 1) (always taken) *)
        (* addloop(x, y) cycles = 2 + 2 + x[3 + 2 + 2 + 5 + (ML - 1)] + 5 + (ML - 1) *)
        (*                      = 9 + (ML - 1) + x(12 + (ML - 1)) *)
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

Arguments N.add _ _ : simpl nomatch.

(* Lifter machinery *)
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
Compute il_list.
(* What gets plugged into the proof *)
Definition lifted_addloop :=
    program_of_list il_list.

(* Correctness proof *)
Local Ltac step := time rv_step.
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
Proof using.
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

(* Timing machinery *)
Definition cycle_count_of_trace (t : trace) : N :=
    List.fold_left N.add (List.map 
        (fun '(e, s) => match e with 
            | Addr a => time_of_addr s a
            | Raise n => max32
            end) t) 0.

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

Definition addloop_timing_invs (_ : store) (p : addr) (x y : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0xc  => Some (s R_T0 = Ⓓx /\ s R_T2 = Ⓓ1 /\ cycle_count_of_trace t = 2 + 2)
    | 0x10 => Some (exists t0, s R_T0 = Ⓓt0 /\ s R_T2 = Ⓓ1 /\ s R_T3 = Ⓓ0 /\ t0 <= x /\
        cycle_count_of_trace t' = 4 + (x - t0) * (12 + (ML - 1)))
        (* 2 + 2 + (x - t0) * (3 + 2 + 2 + (5 + (ML - 1)) *)
    | 0x20 => Some (cycle_count_of_trace t' = 9 + (ML - 1) + x * (12 + (ML - 1)))
        (* 2 + 2 + (5 + (ML - 1)) + x * (3 + 2 + 2 + (5 + (ML - 1))) *)
    | _ => None end
| _ => None
end.

Ltac unfold_decompose :=
    (* unfold decompose_Btype, decompose_Itype, decompose_Jtype, decompose_Rtype, decompose_Stype, decompose_Utype,
        mask_bit_section; simpl (_ .& _). *)
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype decompose_Stype decompose_Utype mask_bit_section];
        simpl (_ .& _).
    (* cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype decompose_Stype 
        decompose_Utype mask_bit_section N.land N.shiftr]. *)
Tactic Notation "unfold_decompose" "in" hyp(H) :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype decompose_Stype decompose_Utype mask_bit_section] in H;
        simpl (_ .& _) in H.
    (* unfold decompose_Btype, decompose_Itype, decompose_Jtype, decompose_Rtype, decompose_Stype, decompose_Utype,
        mask_bit_section in H; simpl (_ .& _) in H. *)

Ltac unfold_time_of_addr :=
    cbv [time_of_addr neorv32_cycles_upper_bound]; simpl.
Tactic Notation "unfold_time_of_addr" "in" hyp(H) :=
    cbv [time_of_addr neorv32_cycles_upper_bound] in H; simpl in H.

Ltac unfold_cycle_count_list :=
    repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single.

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
Proof using.
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

    (* Addr 0xc *)
    destruct PRE as [T0 [T2 Cycles]].
    step. exists a. repeat split; try assumption. lia. 
    psimpl. now rewrite Cycles.

    (* Addr 0x10 *)
    destruct PRE as [t0 [T0 [T2 [T3 [T0_A Cycles_t]]]]].
    step.
    - (* t0 = 0 -> postcondition *)
        rewrite N.eqb_eq in BC; subst. unfold_cycle_count_list.
        unfold_time_of_addr. rewrite T0, T3, Cycles_t. now psimpl.
    - (* t0 <> 0 -> loop again *)
        step. step. step. exists (t0 ⊖ 1). assert (1 <= t0) by (apply N.eqb_neq in BC; lia). repeat split.
            rewrite msub_nowrap; psimpl; lia.
        unfold_cycle_count_list.
        repeat (let Y := fresh "H" in (remember ((time_of_addr _) _) eqn:Y; unfold_time_of_addr in Y; subst)).
        rewrite T0, T3, BC, Cycles_t, N.add_sub_assoc, msub_nowrap, N_sub_distr.
        psimpl. rewrite N.mul_add_distr_r. psimpl.
        rewrite (N.add_sub_assoc 16).

        all: psimpl; (assumption || lia || apply ML_pos).
Qed.

(* Define a policy for addloop with entries for each instruction and permissible jumps including fallthroughs *)
Definition addloop_policy : policy :=
[
  (None, (0, [0xc]));      (* Instruction at 0x8 can fall through to 0xc *)
  (None, (0, [0x10]));     (* Instruction at 0xc can fall through to 0x10 *)
  (None, (0, [0x14; 0x20])); (* Instruction at 0x10 can fall through to 0x14 and jump to 0x20 *)
  (None, (0, [0x18]));    (* Instruction at 0x14 can fall through to 0x18 *)
  (None, (0, [0x1c]));    (* Instruction at 0x18 can fall through to 0x1c *)
  (None, (0, [0x10]))     (* Instruction at 0x1c can jump to 0x10 *)
]%Z.

Compute newcode addloop_policy (List.map Z.of_N add_loop_riscv) 2 2.

(*
    find some timing-critical code as a better example
        - avoid async
    clean up proof
    get ride of decoding reuse
    consider an automated proof writer 
    teach new students on timing proofs rather than correctness
    give picinae talk to trustlab
    hamlen has picinae slides
*)
