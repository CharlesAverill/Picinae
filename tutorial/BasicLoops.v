(** * Basic Loops *)

(* ################################################################# *)
(** * Introduction *)

(** This chapter goes deeper into the structure and meaning of Proofs
    and covers examples of more complicated programs with loops. We'll
    also be using a more sophisticated toy architecture but we'll delay
    its exposition and covering the theoretical and implementation
    underpinnings of Picinae to a later chapter.



    The first half of this chapter introduces the most essential
    elements of Coq's native functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Gallina programs. *)

(* ################################################################# *)
(** * Setting It Up *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Import Picinae_pilbox32.
Require Import NArith.
Require Import Structures.Equalities.
Open Scope N.
Ltac fail_seek ::= idtac.


(* ================================================================= *)
(** ** The AddLoop Program *)

(** Our first example program computes the sum of two numbers by repeatedly
    incrementing one register and decrementing the other until the latter
    is zero.  Again we use a toy architecture and handcrafted IL code.
    The toy architecture we choose this time is specified as a 32 bits
    architecture.  This is a descriptive, not prescriptive, categorization(?)
    of the architecture.  We typically call an architecture X-bits if its
    largest memory range uses X-bit addresses and most of its working
    registers are X-bits.

    At the end of this chapter we'll look at example programs lifted directly
    from real world code. *)
Module Addloop.

Module Addloop1.
Definition addloop (s:store) (a:addr) : option (N * stmt) :=
  match a with
  | 100 => Some(4, Nop)
  | 104 => Some(4, If (BinOp OP_EQ (Var R_R1) (Word 0 32)) (Jmp (Word 120 32)) (Nop))
  | 108 => Some(4, Move R_R1 (BinOp OP_MINUS (Var R_R1) (Word 1 32)))
  | 112 => Some(4, Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 1 32)))
  | 116 => Some(4, Jmp (Word 104 32))
  | 120 => Some(4, Move R_R0 (Var R_R2))
  | _ => None
  end.

(** As before we define our Initial trace condition and our Invariants in dedicated
    section so they can refer to common variables.  We define the exit condition
    afterwards, though this is an arbitrary decision. *)

Section Invs.

  Variable s:store.
  Variable r1 r2:N.
  Definition Entry t xs' := startof t xs' = (Addr 100, s).
  Definition Models := models pil32typctx s.
  Definition TraceConditions s' := s' R_R1 = r1 /\ s' R_R2 = r2.
  Definition Init t xs' := Entry t xs' /\ Models /\ TraceConditions s.

(** Our postcondition is where we start to see the first signs of intrinsic trickiness
    in reasoning about behavior at the machine code level.  This program doesn't simply
    sum two numbers.  It sums them _modulo 32_.  This introduces difficulties both in
    mentally reasoning about proofs as well as constructing proofs.  Later we'll show
    off _psimpl_, our automated modular arithmetic simplifier that can handle a large
    class of modular and bit arithmetic expressions. *)
  Definition postcondition n := n = (r1 + r2) mod 2 ^ 32.

(** This is a CFG of the addloop program:

             100
              |
       +---> 104 ------+
       :      |        :
       :     108       :
       :      |        :
       :     112       :
       :      |        :
       +---- 116       :
                       :
             120 <-----+
              |
             124

    The type of proofs we're exploring say "For all traces that match some starting criteria
    (Init) and a given set of invariants and exit points (Invs and exit) all executions of
    the program

        1. reach an invariant or exit
        2. whenever they reach an invariant the invariant is satisfied and execution continues
           and reaches an invariant or exit."

    Picinae accomplishes the "reaches an invariant or exit" guarantee by creating a proof obligation
    at every non-exit invariant and requiring abstract execution to continue until an exit or invariant
    (possibly the same one) is encountered.

    Specifically, if we place invariants at addresses 100, 104, and 124, and an exit at 124 then
    Picinae will produce 2 subgoals we need to prove - one from address 100 and the other from 104.
    This decomposes the proof into 2 paths of execution:

              100
               |
              104              +---> 104 ------+
                               :      |        :
                               :      |        :
                               :      |        :
                               :      |        :
                               :      |        :
                               +----- +        :
                                               :
                                      + <------+
                                      |
                                     124


    It accomplishes the "invariant is satisfied" guarantee by 1) populating the
    hypothesis space with the proposition of the invariant from which we're starting
    execution and 2) dropping the proof into an ordinary Coq proof whenever
    it reaches the invariant. It replaces the goal with the specified invariant,
    which will often depend on the result of abstract execution. *)


  Definition Invs1 (t:trace) :=
    match t with (Addr a, s)::_ =>
      match a with
      | 100 => Some (TraceConditions s)
      | 104 => Some (((s R_R1) + (s R_R2)) mod 2 ^ 32 = (r1 + r2) mod 2 ^ 32)
      | 124 => Some (postcondition (s R_R0))
      | _ => None
      end
    | _ => None
    end.

End Invs.

Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ =>
    match a with
      124 => true
    | _   => false
    end
  | _ => false
  end.

Theorem addloop_welltyped : welltyped_prog pil32typctx addloop.
Proof. Picinae_typecheck. Qed.

(* TODO: I (ilan) made this tactic, should add it to Picinae_ISA *)
Ltac bound_of MDL V :=
  let H := fresh "BOUND" in
  let opt_w := eval vm_compute in (archtyps V) in
  match opt_w with
  | None => idtac "No such bound"
  | Some ?w => assert (Help: archtyps V = Some w) by reflexivity;
              assert (H:=MDL V w Help); clear Help
   end.

Theorem addloop_partial_correctness:
  forall s t xs' r1 r2
    (INIT: Init s r1 r2 t xs'),
    satisfies_all addloop (Invs1 r1 r2) addloop_exit (xs'::t).
Proof.
  Local Ltac step := pil32_step.

  intros s t xs' r1 r2 (ENTRY & MDL & R1 & R2).
  apply prove_invs.

  (* Base Case *)
  simpl. rewrite ENTRY. step. split; assumption.

  (* Inductive Case *)
  (* Explain the current proof obligation *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply addloop_welltyped).
  clear - PRE MDL. rename t1 into t; rename s1 into s.
  destruct_inv 32 PRE.

  (* 100 -> 104 *)
  destruct PRE as (R1 & R2).
  step.
  subst. reflexivity.

  (* 104 -> 104 / 120 *)
  rename PRE into INV. step.

  (* 104 -> 120 *)
  step.

  rewrite N.eqb_eq in BC. rewrite BC in *.
      rewrite N.add_0_l in INV. rewrite <-INV; clear INV.
      bound_of MDL R_R2. symmetry; now apply N.mod_small.

  (* 104 -> 104 *)
  step. step. step.
  rewrite INV. reflexivity.

Qed.
End Addloop1.

(** What happens if we don't include an invariant anywhere in the loop?

    Considering replacing this with a simpler example that uses nops and an
    unconditional branch. *)

Module AddloopAndBeyond.
Section Invs.
  Variable s:store.
  Variable r1 r2:N.
  Definition Entry t xs' := startof t xs' = (Addr 100, s).
  Definition Models := models pil32typctx s.
  Definition TraceConditions s' := s' R_R1 = r1 /\ s' R_R2 = r2.
  Definition Init t xs' := Entry t xs' /\ Models.

  Definition Invs (t:trace) :=
    match t with (Addr a, s)::_ =>
      match a with
      | 100 => Some (TraceConditions s)
      | 124 => Some (True)
      | _ => None
      end
    | _ => None
    end.
End Invs.

Definition exit (t:trace) :=
  match t with (Addr a, s)::_ =>
    match a with
      124 => true
    | _ => false
  end | _ => false end.

Example addloop_and_beyond s r1 r2: models pil32typctx s ->
  nextinv Addloop1.addloop (Invs r1 r2 ) exit false ((Addr 100, s)::nil).

  (* At 104 - start of the loop *)
  Local Ltac step := pil32_step ; try exact I.

  intro.
  step.
  (* At 104 - start of the loop *)
  step.
  (* At 120 - about to reach postcondition `True` *) step.
  step. step. step.
  step.
  (* At 120 - about to reach postcondition `True` *) step.
  step. step. step.
  step.
  (* At 120 - about to reach postcondition `True` *) step.
  step. step. step.
  step.
  (* At 120 - about to reach postcondition `True` *) step.
  step. step. step.
  (* At 120 - about to reach postcondition `True` *) step.
  (* We loop endlessly because we're searching for the next invariant
     to prove. After 2^32 iterations of the loop we'll be able to show
     a contradiction using all the branch conditions, but in Formal Methods
     we prefer to work smart rather than hard. *)
Abort.
End AddloopAndBeyond.



(** **** Exercise: 1 star, standard, optional (addloop_bookkeeping)

    Modify the invariants and proof for the following addloop to show this version
    is also correct.  This will demonstrate the need for storing bookkeeping information
    in loop invariants.  Most of your work should be copy-pasting.*)

Module Addloop'.
Definition addloop (s:store) (a:addr) : option (N * stmt) :=
  match a with
  | 100 => Some(4, Move (R_R3) (Word 1 32))
  | 104 => Some(4, If (BinOp OP_EQ (Var R_R1) (Word 0 32)) (Jmp (Word 120 32)) (Nop))
  | 108 => Some(4, Move R_R1 (BinOp OP_MINUS (Var R_R1) (Var R_R3)))
  | 112 => Some(4, Move R_R2 (BinOp OP_PLUS  (Var R_R2) (Var R_R3)))
  | 116 => Some(4, Jmp (Word 104 32))
  | 120 => Some(4, Move R_R0 (Var R_R2))
  | _ => None
  end.

Theorem addloop_welltyped : welltyped_prog pil32typctx addloop.
Proof. Picinae_typecheck. Qed.

Section Invs.
  (* CHANGE THESE *)
  Definition Entry := True.
  Definition Models := True.
  Definition Init := True.

  Definition postcondition := False.

  Definition Invs (t:trace) := Some (False).

  Definition exit (t:trace) := true.

End Invs.

Theorem addloop_partial_correctness:
  forall (s:store) t xs' (r1 r2:N) (INIT : Init),
  satisfies_all addloop Invs exit (xs'::t).
Proof.
  (* FILL IN HERE *)
Admitted.
End Addloop'.


End Addloop.

