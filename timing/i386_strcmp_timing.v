Require Import Picinae_i386.
Require Import NArith.
Require Import i386_strcmp.
Require Import Picinae_timing.
Open Scope N.
Open Scope i386_scope.

(* Define variables for the Timing section*)
Definition time_of_stmt (s : option (N * stmt)) : nat :=
    match s with None => 0 | Some (_, s') => match s' with
    | Move _ _ => 2
    | If _ _ _ => 6
    | Jmp _ => 9
    | _ => 0
    end end.

Definition empty_store : store := fun _ => VaN 0 32.

(* Redefine Timing section definitions for brevity*)
Definition program := program store stmt.
Definition timed_program := timed_program store stmt.
Definition timed_program_of_program := timed_program_of_program store stmt time_of_stmt.
Definition program_of_timed_program := program_of_timed_program store stmt.

Tactic Notation "prog_eq_helper" integer(max) constr(Hmax_le) :=
    unfold program_of_timed_program, timed_program_of_program;
    prog_eq_helper store addr empty_store max constr:(Hmax_le).

(* Properties of program *)
Notation strcmp_bound := 36.

(* Begin proofs *)
Theorem strcmp_i386_bounded : 
    program_bounded store strcmp_i386 strcmp_bound.
Proof. prove_bounded. Qed.

Theorem strcmp_i386_conversion_safe : 
    program_of_timed_program (
        timed_program_of_program strcmp_i386 empty_store strcmp_bound
    ) empty_store strcmp_bound = strcmp_i386.
Proof.
    apply functional_extensionality. intro s.
    apply functional_extensionality. intro a.
    (* TODO : Figure a way to pass a Coq variable as an Ltac integer *)
    prog_eq_helper 37 strcmp_i386_bounded.
Qed.

Fixpoint _instruction_time_of_timed_program s (max_addr : nat) (p : timed_program) : nat :=
    match max_addr with 
    | O => match p s 0 with None => 0 | Some (t, st) => t end
    | S n' => (match p s (N.of_nat max_addr) with | None => 0 | Some (t, st) => t end) +
        _instruction_time_of_timed_program s n' p
    end.

Definition instruction_time_of_timed_program s m p :=
    _instruction_time_of_timed_program s (N.to_nat m) p.

Definition injector : Type := timed_program -> timed_program.
Definition timing_policy : Type := nat.

Definition injector_safe_too_strong (inj : injector) :=
    forall (p : timed_program) (tp : timing_policy) s max_addr,
    (instruction_time_of_timed_program s max_addr p <= tp ->
    instruction_time_of_timed_program s max_addr (inj p) <= tp)%nat.

Definition injector_safe (inj : injector) :=
    forall (p : timed_program) (tp : timing_policy) s max_addr indiff outdiff,
    (indiff + instruction_time_of_timed_program s max_addr p = tp ->
    outdiff + instruction_time_of_timed_program s max_addr (inj p) = tp ->
    outdiff <= indiff)%nat.

Definition identity_injector (p : timed_program) : timed_program :=
    p.

Definition injection_safe (input : timed_program) (inj : injector) 
        (wcet : timed_program -> nat) (max_addr : N) (tp : timing_policy) :=
    (wcet input <= tp)%nat ->
    (wcet (inj input) <= tp)%nat.

Definition dumb_injector max_addr (p : timed_program) := 
    insert_timed_instr store stmt time_of_stmt p max_addr empty_store (p empty_store 0) 1.

Definition strcmp_i386_timed : timed_program :=
    timed_program_of_program strcmp_i386 empty_store strcmp_bound.

Theorem identity_injector_safe_strcmp_i386 :
    injection_safe strcmp_i386_timed identity_injector 
        (instruction_time_of_timed_program empty_store strcmp_bound) strcmp_bound 30%nat.
Proof.
    intros ->. lia.
Qed.

Compute instruction_time_of_timed_program empty_store strcmp_bound strcmp_i386_timed.

Compute instruction_time_of_timed_program empty_store 40 (dumb_injector strcmp_bound strcmp_i386_timed).

Ltac pair_val :=
    let x := fresh "x" in
    match goal with
    | [|- (instruction_time_of_timed_program ?s ?n (?inj ?n ?prog) <= ?policy)%nat] =>
        unfold instruction_time_of_timed_program;
        let x := eval compute in (inj n prog) in
        replace (inj n prog) with x by reflexivity; simpl; try lia
    end.

Theorem dumb_injector_safe_strcmp_i386 :
    injection_safe strcmp_i386_timed (dumb_injector strcmp_bound) 
        (instruction_time_of_timed_program empty_store strcmp_bound) strcmp_bound 30%nat.
Proof.
    intros H. pair_val.
Qed.

Theorem identity_injector_safe :
    injector_safe identity_injector.
Proof.
    intros p tp s max_addr indiff outdiff IN OUT. 
    unfold identity_injector in OUT.
    rewrite <- OUT in IN.
    apply PeanoNat.Nat.add_cancel_r in IN. subst. reflexivity.
Qed.

(* what approach to take to compare pairs of execution
    translation-based verification vs translator verification *)
(* find reasonable embedded target *)
