(** #<link rel="stylesheet" href="sf.css"># *)
(** * Basic Loops *)

(* ################################################################# *)
(** * Introduction *)

(** This chapter goes deeper into the structure and meaning of Proofs
    and covers examples of more complicated programs with loops. We'll
    also be using a more sophisticated toy architecture but we'll delay
    its exposition and covering the theoretical and implementation
    underpinnings of Picinae to a later chapter. *)

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
Require Import Lia ZifyN.
Require Import Utf8.
Import PIL32Notations.
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
    (* nop *)
  | 100 => Some(4, Nop)
    (* :addloop *)
    (* beqz r1 :done *)
  | 104 => Some(4, If (BinOp OP_EQ (Var R_R1) (Word 0 32)) (Jmp (Word 120 32)) (Nop))
    (* sub r1 0x1 *)
  | 108 => Some(4, Move R_R1 (BinOp OP_MINUS (Var R_R1) (Word 1 32)))
    (* add r2 0x1 *)
  | 112 => Some(4, Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 1 32)))
    (* jmp :addloop *)
  | 116 => Some(4, Jmp (Word 104 32))
    (* :done *)
    (* mov r2 r0 *)
  | 120 => Some(4, Move R_R0 (Var R_R2))
  | _ => None
  end.

(** As before we define our Initial trace condition, our Invariants, and exits
    in a dedicated section so they can refer to common variables. *)

Section Invs.

  Variable s:store.
  Variable r1 r2:N.
  Definition Entry t xs' := startof t xs' = (Addr 100, s).
  Definition Models := models pil32typctx s.
  Definition TraceConditions s' := s' R_R1 = r1 /\ s' R_R2 = r2.
  Definition Init t xs' := Entry t xs' /\ Models /\ TraceConditions s.

(** Our postcondition is where we start to see the first signs of the intrinsic trickiness
    in reasoning about behavior at the machine code level.  This program doesn't simply
    sum two numbers.  It sums them _modulo 32_.  This introduces difficulties both in
    mentally reasoning about proofs as well as constructing proofs.  At this level it is
    a common phenomenon to find yourself looking at a simple equation and wondering "wait,
    is this actually even true?" Later we'll show off _psimpl_, our automated modular
    arithmetic simplifier that can handle a large class of modular and bit arithmetic
    expressions. *)
  Definition postcondition n := n = (r1 + r2) mod 2 ^ 32.

(** This is a control flow graph (CFG) of the addloop program showing which instructions
    execute after which other instructions.  It shows that the instruction at address 100
    always falls through to the instruction at 104, the instruction at 104 may fall through to
    108 or branch to 120, the instruction at 116 always jumps to 104, and all other instructions
    fall through similarly to 100:

<<
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
>>

    The type of proofs we're exploring say "For all traces that match some starting criteria
    (Init) and a given set of invariants and exit points (Invs and exit) all executions of
    the program

        1. reach an invariant or exit
        2. whenever they reach an invariant the invariant is satisfied and execution continues
           and reaches an invariant or exit."

    Picinae accomplishes the "reaches an invariant or exit" guarantee by creating a proof obligation
    at every non-exit invariant and requiring abstract execution to continue until an exit or invariant
    (possibly the same one) is encountered.  This is the function of the `destruct_invs XX.` tactic
    in our proofs.

    Specifically, if we place invariants at addresses 100, 104, and 124, and an exit at 124 then
    Picinae will produce 2 subgoals we need to prove - one from address 100 and the other from 104.
    This decomposes the proof into 2 paths of execution:

<<
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
>>

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

Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ =>
    match a with
      124 => true
    | _   => false
    end
  | _ => false
  end.

End Invs.

Theorem addloop_welltyped : welltyped_prog pil32typctx addloop.
Proof. Picinae_typecheck. Qed.

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

  rewrite N.eqb_eq in BC. rewrite BC in *. elimstore.
      rewrite N.add_0_l in INV. rewrite <-INV; clear INV.
      rewrite N.mod_small; lia.

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
  (* li r3 0x1 *)
  | 100 => Some(4, Move (R_R3) (Word 1 32))
  (* :loop *)
  (* beqz r1 :exit *)
  | 104 => Some(4, If (BinOp OP_EQ (Var R_R1) (Word 0 32)) (Jmp (Word 120 32)) (Nop))
  (* sub r1 r1 r3 *)
  | 108 => Some(4, Move R_R1 (BinOp OP_MINUS (Var R_R1) (Var R_R3)))
  (* add r2 r2 r3 *)
  | 112 => Some(4, Move R_R2 (BinOp OP_PLUS  (Var R_R2) (Var R_R3)))
  (* jmp :loop *)
  | 116 => Some(4, Jmp (Word 104 32))
  (* :exit *)
  (* mov r0 r2 *)
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

(** Exercise:4 stars, standard, optional (sumton)

    Prove the following iterative sum adds up to the closed form expression
   [(n*(n+1))/2 mod 2^32] when n>1 is given as input to R_R1. *)
Module SumToN.
Definition sumton (s:store) (a:addr) : option (N * stmt) :=
  match a with
  (* li r3 0x1 *)
  | 100 => Some(4, Move (R_R3) (Word 1 32))
  (* li r2 0x0 *)
  | 104 => Some(4, Move (R_R2) (Word 0 32))
  (* :loop *)
  (* blt r1 r3 :exit *)
  | 108 => Some(4, If (BinOp OP_LT (Var R_R1) (Var R_R3)) (Jmp (Word 124 32)) (Nop))
  (* add r2 r2 r3 *)
  | 112 => Some(4, Move R_R2 (BinOp OP_PLUS (Var R_R2) (Var R_R3)))
  (* add r3 r3 0x1 *)
  | 116 => Some(4, Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32)))
  (* jmp :loop *)
  | 120 => Some(4, Jmp (Word 108 32))
  (* :exit *)
  (* mov r0 r2 *)
  | 124 => Some(4, Move R_R0 (Var R_R2))
  (* ret *)
  | 128 => Some(4, Jmp (Var R_LR))
  | _ => None
  end.

Theorem sumton_welltyped : welltyped_prog pil32typctx sumton.
Proof. Picinae_typecheck. Qed.

Section Invs.
  (* Change the Init, postcondition, and Invs functions as necessary. *)
  Variable s : store.
  Definition Entry t xs' := startof t xs' = (Addr 100, s).
  Definition Models := models pil32typctx s.
  Definition Init t xs' n := Entry t xs' /\ Models /\ s R_R1 = n.

  Definition postcondition (s':store) (n:N) := True.

  Definition Invs n (t:trace) := match t with (Addr a, s)::_ =>
    match a with
    | 100 => Some (s R_R1 = n)
    | 116 => Some (True)
    | 128 => Some (postcondition s n)
    | _ => None
    end | _ => None end.

  Definition exit (t:trace) := match t with (Addr 128,_)::_ => true | _=> false end.

End Invs.

Theorem sumton_partial_correctness:
  forall (s:store) t xs' (n:N) (INIT : Init s t xs' n),
  satisfies_all sumton (Invs n) exit (xs'::t).
Proof.
  Local Ltac step := pil32_step.
  (* FILL IN HERE *)
Admitted.
End SumToN.

(** Exercise:4 stars, standard, optional (factorial)

    Prove the following loop computes the lower 32 bits of the factorial
    of the value initially in R_R3.*)
Module Factorial.

Definition factorial (s:store) (a:addr) : option (N * stmt) :=
  match a with
    (* li r1 0x1 *)
  | 100 => Some(4, Move R_R1 (Word 1 32))
    (* beqz r3 :exit *)
  | 104 => Some(4, If (BinOp OP_EQ (Var R_R3) (Word 0 32)) (Jmp (Word 140 32)) Nop)
    (* li r2 0x1 *)
  | 108 => Some(4, Move R_R2 (Word 1 32))
    (* nop *)
  | 112 => Some(4, Nop)
    (* :loop *)
    (* beq r2 r3 :loop_done *)
  | 116 => Some(4, If (BinOp OP_EQ (Var R_R2) (Var R_R3)) (Jmp (Word 136 32)) Nop)
    (* mul r1 r1 r2 *)
  | 120 => Some(4, Move R_R1 (BinOp OP_TIMES (Var R_R1) (Var R_R2)))
    (* add r2 r2 0x1 *)
  | 124 => Some(4, Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 1 32)))
    (* jmp :loop *)
  | 128 => Some(4, Jmp (Word 116 32))
    (* nop *)
  | 132 => Some(4, Nop)
    (* :loop_done *)
  | 136 => Some(4, Move R_R1 (BinOp OP_TIMES (Var R_R1) (Var R_R2)))
    (* :exit *)
    (* nop *)
  | 140 => Some(4, Nop)
  | _ => None
  end.

Theorem factorial_welltyped : welltyped_prog pil32typctx factorial.
Proof. Picinae_typecheck. Qed.

Section Invs.
  (* For this exercise you only need to change the loop invariant in Invs. *)
  Variable s : store.
  Definition Entry t xs' := startof t xs' = (Addr 100, s).
  Definition Models := models pil32typctx s.
  Definition Init t xs' r3 := Entry t xs' /\ Models /\ s R_R3 = r3.

  Fixpoint natfactorial (n:nat) :=
    match n with O => 1 | S n' => (N.of_nat n) * (natfactorial n') end.
  Definition postcondition s' r3 := s' R_R1 = natfactorial (N.to_nat r3) mod 2^32.

  Definition Invs r3 (t:trace) := match t with (Addr a, s)::_ =>
    match a with
    | 100 => Some (s R_R3 = r3)
    | 124 => Some (True)
    | 140 => Some (postcondition s r3)
    | _ => None
    end | _ => None end.


  Definition exit (t:trace) := match t with (Addr 140, _)::_ => true | _ => false end.

End Invs.

(** You might find these lemmas helpful in your proofs. *)
Lemma natfactorial_pred:
  forall n, natfactorial n * N.of_nat (S n) = natfactorial (S n).
Proof.
  induction n.
  - reflexivity.
  - unfold natfactorial at 2. rewrite N.mul_comm, N.mul_cancel_l; try lia.
    rewrite <-IHn, N.mul_comm, N.mul_cancel_l; try lia.
    reflexivity.
Qed.

Lemma S_to_nat :
  forall n, N.to_nat (1+n) = S (N.to_nat n).
Proof.
  intros. now rewrite N.add_1_l, N2Nat.inj_succ.
Qed.

Lemma Nsucc_S :
  forall n, N.succ n = N.of_nat (S (N.to_nat n)).
Proof.
  intros.
  now rewrite Nat2N.inj_succ, N2Nat.id.
Qed.

Lemma mod_mono_r :
  forall x b y, x < y -> x mod b < y.
Proof.
  intros. eapply N.le_lt_trans.
  apply N.Div0.mod_le.
  assumption.
Qed.

(** This is the theorem you need to prove. *)
Theorem factorial_partial_correctness:
  forall (s:store) t xs' (r3:N) (INIT : Init s t xs' r3),
  satisfies_all factorial (Invs r3) exit (xs'::t).
Proof.
  Local Ltac step := pil32_step.
  (* FILL IN HERE *)
Admitted.
End Factorial.


(** **** Exercise:4 stars, standard, recommended (wcscpy_partial_correctness)

    Specify and prove the partial correctness of this simplified wcscpy
    implementation.  This is the first usage of memory in this tutorial, and not
    only that, but of memory-writes.  We've placed the invariants at the locations
    we used to prove this correct and left some of the loop-invariant intact with
    additional explanation below.

    You'll find many abstractions provided by Picinae are useful for this exercise.
    Below is a complete list of what we used;  you can find more details about
    these abstractions in the chapter [AbsAndPracs].

      * [wstrlen] (wrapped up in the [strlen'] definition below)
      * [wnilfree]
      * [overlap] and [~ overlap]
      * mem_region_unchanged
*)
Module wcscpy.
(** r1 - pointer to source wide character string being copied.
    r0 - pointer to destination *)
Definition wcscpy (s:store) (a:addr) : option (N * stmt) :=
  match a with
  (* 0x00100000: mov r2,#0x0 *)
  | 1048576 => Some (4, Move R_R2 (Word 0 32))

  (* 0x00100004: ldr r3,[r1, r2, LSL #0x0] *)
  | 1048580 => Some (4,
    Move R_R3 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32)
      (BinOp OP_PLUS (Var R_R1) (BinOp OP_LSHIFT (Var R_R2) (Word 0 32))) LittleE 4)))

  (* 0x00100008: str r3,[r0, r2, LSL #0x0] *)
  | 1048584 => Some (4,
    Move V_MEM32 (Store (Var V_MEM32)
    (BinOp OP_PLUS (Var R_R0) (BinOp OP_LSHIFT (Var R_R2) (Word 0 32)))
    (Var R_R3)
    LittleE 4)
  )

  (* 0x0010000c: add r2,r2,#0x4 *)
  | 1048588 => Some (4,
    Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 4 32)))

  (* 0x00100010: cbnz r3,0x00100004 *)
  | 1048592 => Some (4,
    If (BinOp OP_NEQ (Var R_R3) (Word 0 32)) (
      Jmp (Word 1048580 32)
    ) (* else *) (
      Nop
    )
  )

  (* 0x00100014: ret *)
  | 1048596 => Some (4, Nop)

  | _ => None
  end.

Theorem wcscpy_welltyped : welltyped_prog pil32typctx wcscpy.
Proof. Picinae_typecheck. Qed.

Definition strlen' := wstrlen 32 LittleE.

Section Invs.
  Variable s:store.
  Variable mem psrc pdest len:N.
  (* CHANGE THESE *)
  Definition Entry t xs' := startof t xs' = (Addr 0x00100000, s).
  Definition Models := models pil32typctx s.
  (** Replace the [True] in Init with your own initial conditions *)
  Definition Init t xs' := Entry t xs' /\ Models /\
    s V_MEM32 = mem /\ s R_R0 = pdest /\ s R_R1 = psrc
    /\ True.

  (** Replace the [True] in the postcondition with your own initial conditions *)
  Definition postcondition (s:store) :=
    exists m, s V_MEM32 = m /\ True.

  Definition Invs (t:trace) := match t with (Addr a, s)::_ =>
  match a with
  | 0x00100000 => Some (s V_MEM32 = mem /\ s R_R0 = pdest /\ s R_R1 = psrc
                        /\ True)
  (** TODO: Explain the exists m, s V_MEM32 = m clause *)
  | 0x00100004 => Some (exists m, s V_MEM32 = m
                        /\ strlen' m psrc len
                        /\ True)
  | 0x00100014 => Some (postcondition s)
  | _ => None end | _ => None end.

  Definition exit (t:trace) := match t with (Addr 0x00100014,_)::_ => true | _ => false end.

End Invs.

Theorem wcscpy_partial_correctness:
  forall (s:store) t xs' (mem psrc pdest len:N) (INIT : Init s mem psrc pdest t xs'),
  satisfies_all wcscpy (Invs mem psrc pdest len) exit (xs'::t).
Proof.
  Local Ltac step := pil32_step.
  intros s t xs' mem psrc pdest len (ENTRY & MDL & MEM & LEN & NOV).
  apply prove_invs.

  (* Base Case *)
  simpl. rewrite ENTRY. step. repeat (assumption || split).

  (* Inductive Case *)
  (* Explain the current proof obligation *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply wcscpy_welltyped).
  clear - PRE MDL. rename t1 into t; rename s1 into s.
  destruct_inv 32 PRE.
Abort.
End wcscpy.

