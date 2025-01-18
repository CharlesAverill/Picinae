(** * Motivation *)

(* ################################################################# *)
(** * Introduction *)

(** This introduction demonstrates a proof of program behaviour,
    the primary use case of Picinae, and explains how this fits
    into the reliable software ecosystem

    Predicting software behavior is important.

    Driving on a cliff analogy for software reliability:

      *  Unit/Integration Testing is like opening your eyes
      *  Runtime exception handling is like guard rails
      *  Model Checking is like simulation
      *  Formal Proofs are like total knowledge of all configurations of
         the universe.  You can safely drive with your eyes closed.


    The first part of this chapter covers the 3 steps required to
    start writing proofs about programs for a specific architecture.
    This includes 1) Architecture Specification, 2) Picinae Module
    instantiation, and 3) LTac machinery definition. Afterwards we
    use all of it to show how to prove a property of a simple
    program. *)

(* ################################################################# *)
(** * Setting It Up *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
Require Import NArith.
Require Import Structures.Equalities.
Open Scope N.

(* ================================================================= *)
(** ** Architecture Specification *)

(** Before we reason about a program we need to define the architecture
    this program is for.  This architecture specifies the registers and
    their sizes,  the different memories and their sizes,  word size,
    and the default endianness.  This can represent a physical or virtual
    machine.

    Here we use a minimal architecture specification hand crafted for
    this demonstration.  We will refer to this architecture as "a64" and
    "A64" in the code to make it clear what definitions and operations
    are architecture specific. *)

(** _a64var_ enumerates the registers and memories available in our model.

    Subregisters, like the lower 32-bits of a 64 bit register, are not
    modeled.  It's easier and safer to change the way a 64-bit register is used in
    a program to emulate the 32-bit subregister's behavior than it is to
    model them as two distinct registers and ensure that their values
    are coherent. *)

Inductive a64var :=
  | V_MEM
  | R_R0 | R_R1 | R_R2.

(** At this point there is no semantics associated with V_MEM, R_R0, etc.
    Each one may later be defined as a 1-bit register or a 42-bit register.
    They are just unique identifiers.

    The function _a64typctx_ is what we use to establish the architectural
    meanings of the different _a64var_'s.  It takes as input an _a64var_
    and optionally returns its bitwidth. Please note the unusual representation
    of memery:

      NB. Memory is just a number represented by the concatenation of all bits.
          Thus its bitwidth is 8 times the number of bytes.
*)

Definition a64typctx (id:a64var) : option N :=
  match id with
  | V_MEM => Some (8*2^64)
  | R_R0 | R_R1 | R_R2 => Some (64)
  end.

(* ================================================================= *)
(** ** Module Instantiation *)

(** Picinae makes extending its powers to
    new architectures simple. Once we've specified an architecture, which
    is usually a simple copy-paste-modify operation, we instantiate the
    core modules with the architecture and we're ready to start writing
    proofs!

    We'll skip over these details here and discuss them in Chapter X. *)

Module MiniA64VarEq <: MiniDecidableType.
  Definition t := a64var.
  Definition eq_dec (v1 v2:a64var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.
  Arguments eq_dec v1 v2 : simpl never.
End MiniA64VarEq.

Module A64Arch <: Architecture.
  Module Var := Make_UDT MiniA64VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := a64typctx.

  Definition mem_readable (s:store) (a:addr) := True.
  Definition mem_writable (s:store) (a:addr) := True.
End A64Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_a64 := PicinaeIL A64Arch.
Export IL_a64.
Module Theory_a64 := PicinaeTheory IL_a64.
Export Theory_a64.
Module Statics_a64 := PicinaeStatics IL_a64 Theory_a64.
Export Statics_a64.
Module FInterp_a64 := PicinaeFInterp IL_a64 Theory_a64 Statics_a64.
Export FInterp_a64.

Module PSimpl_a64 := Picinae_Simplifier_Base IL_a64.
Export PSimpl_a64.
Module PSimpl_a64_v1_1 := Picinae_Simplifier_v1_1 IL_a64 Theory_a64 Statics_a64 FInterp_a64.
Ltac PSimpl_a64.PSimplifier ::= PSimpl_a64_v1_1.PSimplifier.

Module ISA_a64 := Picinae_ISA IL_a64 PSimpl_a64 Theory_a64 Statics_a64 FInterp_a64.
Export ISA_a64.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "a64_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "a64_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "a64_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "a64_psimpl" := psimpl_goal.
Ltac step := ISA_step.
(* ================================================================= *)
(** ** Ltac Machinery*)

(** Picinae uses a lot of machinery to smooth the process of writing proofs
    about machine code. Setting up this machinery is just another short
    copy-paste-modify task.

    We set this up here stripped of its documentation to get to the good
    part of the demo.  *)

Ltac simpl_memaccs H ::=
  try reflexivity.
Ltac fail_seek ::= idtac.

(* ================================================================= *)
(** ** A Simple Program Proof *)

(** With the modules and machinery set up we can move on to showing how a simple
    program proof works.  Picinae programs can be represented in many ways, but each
    way amounts to a function mapping a store and an address to an IL statement
   for the symbolic interpreter to execute, plus a number of bytes to step forward
   if execution control falls through.

    The following program is a hand written example, it adds 1 to the value stored in
    the value stored in register 2 (_R_R2_), shifts it left, and stores the result in
   register 1. It maps the addresses 100, 104 and 108 to the made-up number of bytes
   the instruction takes up in memory (4 in each case) and a single Picinae IL statement
   that moves the result of an expression into a register.

   The formal semantics of Picinae IL statements are covered in Chapter X.
*)

Definition demo_program (_:store) (a:addr) : option (N * stmt) :=
  match a with
  | 100 => Some (4, Move (R_R2) (BinOp OP_PLUS (Var R_R2) (Word 1 64)))
  | 104 => Some (4, Move (R_R2) (BinOp OP_LSHIFT (Var R_R2) (Word 1 64)))
  | 108 => Some (4, Move (R_R0) (Var R_R2))
  | _ => None
  end.

(** We'll also need a proof that this program is well typed. We'll get into what that
    means and why we need it in the next chapter. *)
Theorem demo_program_welltyped : welltyped_prog a64typctx demo_program.
Proof.
  Picinae_typecheck.
Qed.

(** Next we'll define a function that maps an _execution trace_ to an _invariant_.
    Briefly, an execution trace is a list of states that a program has passed through
    with the current state stored in the head; an invariant is a predicate over
    traces that we wish to prove.

    Informally, the structure of our proof will look like this...

        For our program p:
        given a prefix trace t0 that satisfies condition Init, a partial function Invs from
        traces to predicates, and a function that defines when a trace has "exited"
        we show that all traces t = t1 ++ t0 that continue t0 either exit or reach a trace_
        for which Invs t is defined, and whenever Invs t is defined it is satisfied.

    The core components are:

        1. Init - a predicate over traces that defines our starting conditions.
        2. Invs - a partial mapping from traces to a predicate over the input trace.
        3. Exits - a total mapping from traces to whether they have exited.

    We'll create them in order... *)

Definition Init (t:trace) s xs' r2 :=
  startof t xs' = (Addr 100, s)
  /\ models a64typctx s
  /\ s R_R2 = r2
  .

(** This _Init_ function states that

      1. the trace starts at address 100 and in state s, and
      2. the value in register 2 is r2.

   Next we'll define the _Invs_ function that specifies the properties of traces that we want
   to prove.  Coming up with these properties, or _invariants_, is the second hardest part of
   proving properties of assembly code, right after proving properties of modular arithmetic :) *)

(** To start we'll open a new section so we can define some variables and use them in our definitions
    without maintaining long parameter lists. Although this isn't very useful in this demonstration
    we've found that this helps with readability and understandibility in realistic endeavors. *)

Section Invs.

(** We define a variable that represents the initial contents of the R2 register. *)

  Variable r2 : N.

(** We define our postcondition separately for clarity and reusability. We could inline it
    in our _Invs_ function below but then finding it when developing or auditing code would
    be more cumbersome.  This way we can also reuse it easily in helper lemmas about the
    postcondition. *)
  Definition postcondition (n:N) : Prop := N.even n = true.


(** Next we define the _Invs_ partial function that maps traces to the invariants they satisfy.
    The propositions herein will be the proof obligations we see in our proof about the
    behavior of this program.

   The trickiest part is that we can't use the values of our store directly as natural
   numbers in propositions because they have the structure _VaN n b_ for some n and b.
   Instead we use an existential variable that we bind to _n_ and then use this variable
   as the value of the register in propositions, e.g. in _even n_ below.

    We've defined the entry point of our program as address 100, so it is helpful to put an
    invariant there. This will typically be a subset of our initial assumptions, specifically
    those that tell us about the state of the trace upon entry. If we do not include them
    then we will lose that information when we destruct the proof into its constituent parts.
    We'll explain more about that in the next chapter where we look at proofs for more
    complex programs. *)

  Definition Invs (t:trace) : option Prop :=
    match t with (Addr a, s)::_ =>
      match a with
      | 100 => Some (s R_R2 = r2)
      | 112 => Some (postcondition (s R_R0))
      | _ => None
      end
    | _ => None end.
End Invs.

(** Lastly we define the exit points in our programs, a total function from traces to a bool
    indicating whether the trace is at an exit.  This is used to terminate the proof and signal
    that traces at this point need not reach and satisfy another invariant.

    We set address 112 as our only exit point, this is the address following the last.  If we
    set it as the final instruction then that instruction will not execute. *)
Definition exit (t:trace) : bool :=
  match t with (Addr a, _)::_ =>
    match a with
      112 => true
    | _ => false
    end
  | _ => false
  end.

(** Now that we've defined 1) the initial conditions of traces we're reasoning about, 2) the
    properties we will prove they satisfy and 3) the exit points that mark future execution
    beyond the scope of our proofs we are finally ready to write the proof! *)

Theorem prog_partial_correctness :
  forall s t xs' r2 (INIT: Init t s xs' r2),
    satisfies_all demo_program (Invs r2) exit (xs'::t).
Proof.
  intros. destruct INIT as (ENTRY & MDL & R2).
  apply prove_invs.

  (* Base Case *)
  simpl. rewrite ENTRY. step. assumption.

  (* Inductive Case *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply demo_program_welltyped).
  clear - PRE MDL. rename t1 into t; rename s1 into s.
  destruct_inv 64 PRE.

  step. step. step.

  (* Postcondition *)
  rewrite update_updated.
  destruct (1 + r2) eqn:Eq.
    reflexivity.
    apply mp2_even. all: easy.
Qed.

(** After some initial setup we see how Picinae uses Coq as an abstract execution engine.
    Each _step_ call executes one machine instruction at the current address and replaces
    the goal with each possible result of the instruction call.

    We'll cover what's going on with the proof, including the mystery of xs', in the following chapter.
    This is enough to show off the most basic user experience of proving properties of programs with
    Picinae.

    Before we wrap up we'd like to impress upon you Picinae's abstract execution ability with
    one more example.  In the program below, the instruction at address 0 jumps to 1 of 6
    possible destinations or falls through depending on a sequence of condition checks. *)

Definition multijump (s:store) (a:addr) : option (N * stmt) :=
  match a with
  | 0 => Some(1, If (BinOp OP_EQ (Var R_R0) (Word 0 64)) (Jmp (Word 1 64))
                 (If (BinOp OP_EQ (Var R_R0) (Word 1 64)) (Jmp (Word 2 64))
                 (If (BinOp OP_EQ (Var R_R0) (Word 2 64)) (Jmp (Word 3 64))
                 (If (BinOp OP_EQ (Var R_R0) (Word 3 64)) (Jmp (Word 4 64))
                 (If (BinOp OP_EQ (Var R_R0) (Word 4 64)) (Jmp (Word 5 64))
                 (If (BinOp OP_EQ (Var R_R0) (Word 5 64)) (Jmp (Word 6 64)) (Nop)))))))
  | 1 => Some(1, Exn 1)
  | 2 => Some(1, Exn 2)
  | 3 => Some(1, Exn 3)
  | 4 => Some(1, Exn 4)
  | 5 => Some(1, Exn 5)
  | 6 => Some(1, Exn 6)
  | _ => None
  end.

(** Let's set up an environment where we start at address 0. *)

Example jumpy s : nextinv multijump (fun _ => None) (fun _ => false) false ((Addr 0, s)::nil).

(** Now we take a step. *)

step.

(** Wow!  Look at all of those goals!  Picinae interpreted the instruction and generated a list
    of 7 subgoals corresponding to all possible evaluations and exits, including the fall through,
    and updated the contexts of each with a Branch Condition (BC) that shows the conditions necessary
    for this trace.

    If we take a close look we see that the goal at the bottom (subgoal 7) is exactly the same as the goal
    at the top (subgoal 1).  By moving the subgoals around to inspect it we can see all the branch
    conditions that were necessary to hold for the control to fall through.
 *)
all:cycle -1.
Abort.
