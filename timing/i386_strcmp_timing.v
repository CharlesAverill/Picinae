Require Import Picinae_i386.
Require Import NArith.
Require Import i386_strcmp.
Require Import i386Timing.
Open Scope N.
Open Scope i386_scope.

Module strcmp_toa.
    Definition time_of_addr (a : addr) : nat :=
        match a with
        | 0 => 7
        | 4 => 15
        | 8 => 2
        | _ => 8
        end.
End strcmp_toa.

Module i386T := MakeTimingContents i386Timing strcmp_toa.
Import i386T.

(* Properties of program *)
Notation strcmp_bound := 36.

(* Show that the program is bounded - that it has a finite representation *)
Theorem strcmp_i386_bounded : 
    program_bounded strcmp_i386 strcmp_bound.
Proof. prove_bounded. Qed.

(* Show that the timed-program-generator is correct for strcmp *)
Theorem strcmp_i386_conversion_safe : 
    timed_conversion_safe strcmp_i386 strcmp_bound.
Proof using.
    intro s.
    apply functional_extensionality. intro s'.
    apply functional_extensionality. intro a.
    (* TODO : Figure a way to pass a Coq variable as an Ltac integer *)
    prog_eq_helper 37 strcmp_i386_bounded.
Qed.

(* Bad estimate of worst-case execution time (WCET) *)
Fixpoint _instruction_time_of_timed_program s (max_addr : nat) (p : timed_program) : nat :=
    match max_addr with 
    | O => match p s 0 with None => 0 | Some (t, st) => t end
    | S n' => (match p s (N.of_nat max_addr) with | None => 0 | Some (t, st) => t end) +
        _instruction_time_of_timed_program s n' p
    end.

Definition instruction_time_of_timed_program s m p :=
    _instruction_time_of_timed_program s (N.to_nat m) p.

(* Definitions for code injectors *)
Definition injector : Type := timed_program -> timed_program.
Definition timing_policy : Type := nat.

(* A poor definition of safety for a real-time code injector *)
Definition injector_safe_too_strong (inj : injector) :=
    forall (p : timed_program) (tp : timing_policy) s max_addr,
    (instruction_time_of_timed_program s max_addr p <= tp ->
    instruction_time_of_timed_program s max_addr (inj p) <= tp)%nat.

(* A better definition of safety *)
Definition injector_safe (inj : injector) :=
    forall (p : timed_program) (tp : timing_policy) s max_addr indiff outdiff,
    (indiff + instruction_time_of_timed_program s max_addr p = tp ->
    outdiff + instruction_time_of_timed_program s max_addr (inj p) = tp ->
    outdiff <= indiff)%nat.

(* A different approach at safety - prove safety for injector specific 
    input-output pairs rather than all input-output pairs *)
Definition injection_safe (input : timed_program) (inj : injector) 
        (wcet : timed_program -> nat) (max_addr : N) (tp : timing_policy) :=
    (wcet input <= tp)%nat ->
    (wcet (inj input) <= tp)%nat.

(* The cycle-annotated form of strcmp *)
Definition strcmp_i386_timed : timed_program :=
    timed_program_of_program strcmp_i386 empty_store strcmp_bound.

(* Example 1: The identity injector *)
Definition identity_injector (p : timed_program) : timed_program :=
    p.

Theorem identity_injector_safe_strcmp_i386 :
    injection_safe strcmp_i386_timed identity_injector 
        (instruction_time_of_timed_program empty_store strcmp_bound) strcmp_bound 30%nat.
Proof.
    intros ->. lia.
Qed.

Theorem identity_injector_safe :
    injector_safe identity_injector.
Proof.
    intros p tp s max_addr indiff outdiff IN OUT. 
    unfold identity_injector in OUT.
    rewrite <- OUT in IN.
    apply PeanoNat.Nat.add_cancel_r in IN. subst. reflexivity.
Qed.

(* Example 2: Duplicate the first instruction *)
Definition dumb_injector max_addr (p : timed_program) := 
    insert_timed_instr p max_addr empty_store (p empty_store 0) 1.

(* A general-purpose tactic for proving correctness of input-output pair injections *)
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
        (instruction_time_of_timed_program empty_store strcmp_bound) strcmp_bound 128%nat.
Proof using.
    intros H. pair_val.
Qed.

Definition edge : Type := addr * addr.

Definition exp_processor (a : addr) (e : exp) : option edge :=
    match e with Word n _ => Some (a, n) | Var _ => Some (a, strcmp_bound + 1) | _ => None end.

Fixpoint edge_generator (a : addr) (s : stmt) : list edge :=
    match s with
    | Seq s1 s2 | If _ s1 s2 => edge_generator a s1 ++ edge_generator a s2
    | Jmp e => match exp_processor a e with Some x => x :: nil | None => nil end
    | _ => nil
    end.

Fixpoint dag_generator (p : program_list) : list edge :=
    match p with
    | nil => nil
    | (src, oss) :: t => match oss with Some (_, s) =>
        (edge_generator src s) ++ dag_generator t
        | _ => dag_generator t
        end
    end.

Compute dag_generator (list_of_program strcmp_i386 empty_store (N.to_nat strcmp_bound)).
