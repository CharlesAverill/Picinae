(* Example proofs using Picinae for Intel x86 Architecture

   Copyright (c) 2023 Kevin W. Hamlen
   Computer Science Department
   The University of Texas at Dallas

   Any use, commercial or otherwise, requires the express permission of
   the author.

   To run this module, first load and compile:
   * Picinae_syntax
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_slogic
   * Picinae_i386
   * strcmp_i386
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import i386_strcmp.

Import X86Notations.
Open Scope N.

(* The x86 lifter models non-writable code. *)
Theorem strcmp_nwc: forall s2 s1, strcmp_i386 s1 = strcmp_i386 s2.
Proof. reflexivity. Qed.

(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strcmp_welltyped: welltyped_prog x86typctx strcmp_i386.
Proof.
  Picinae_typecheck.
Qed.

(* Example #2: Memory safety
   Strcmp contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem strcmp_preserves_memory:
  forall_endstates strcmp_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.



(* Example #3: Architectural calling convention compliance
   Strcmp does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strcmp_preserves_ebx:
  forall_endstates strcmp_i386 (fun _ s _ s' => s R_EBX = s' R_EBX).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strcmp_preserves_readable:
  forall_endstates strcmp_i386 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Proving that strlen preserves ESP is our first example of a property that
   requires stepwise symbolic interpretation of the program to verify.  We must
   first identify the instruction addresses that we wish to consider as subroutine
   exit points (usually the return instructions).  This is where post-conditions
   are placed, and where symbolic execution will stop during the proof. *)
Definition strcmp_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 22 | 36 => true
  | _ => false
  end | _ => false end.

(* Next we define a set of invariants, one for each program point.  In this case,
   all program points have the same invariant, so we define the same for all. *)
Definition esp_invs (esp0:N) (t:trace) :=
  match t with (Addr _,s)::_ =>
    Some (s R_ESP = Ⓓesp0)
  | _ => None end.

(* Now we pose a theorem that asserts that this invariant-set is satisfied at
   all points in the subroutine.  The "satisfies_all" function asserts that
   anywhere an invariant exists (e.g., at the post-conditions), it is true. *)
Theorem strcmp_preserves_esp:
  forall s esp0 t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s)
         (ESP: s R_ESP = Ⓓesp0),
  satisfies_all strcmp_i386 (esp_invs esp0) strcmp_exit ((x',s')::t).
Proof.
  intros.

  (* Use the prove_invs inductive principle from Picinae_theory.v. *)
  apply prove_invs.

  (* We must first prove the pre-condition, which says that the invariant-set is
     satisfied on entry to the subroutine.  This is proved by assumption ESP. *)
  simpl. rewrite ENTRY. x86_step. exact ESP.

  (* Now we enter the inductive case, wherein Coq asks us to prove that the invariant-set
     is preserved by every (reachable) instruction in the program.  Before breaking the
     goal down into many cases (one for each instruction in this case), it is wise to
     simplify and/or remove anything in the context that is unnecessary. In order for
     symbolic interpretation to succeed, the proof context must reveal the values of all
     relevant variables in store s1 (which denotes the store on entry to each instruction
     for which the goal must be proved).  The only two variables in our invariant-set are
     ESP and MEM.  The value of ESP is already revealed by pre-condition (PRE), and we
     can get the value of MEM using our previously proved strlen_preserves_memory theorem. *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strcmp_welltyped).
  clear - PRE MDL. rename t1 into t. rename s1 into s.

  (* We are now ready to break the goal down into one case for each invariant-point.
     The destruct_inv tactic finds all the invariants defined by the invariant-set
     in a precondition hypothesis (PRE).  Its first argument is the address bitwidth
     of the ISA (32 bits in this case). *)
  destruct_inv 32 PRE.

  (* Now we launch the symbolic interpreter on all goals in parallel. *)
  all: x86_step.

  (* Note that we wind up with more goals that we started with, since some of the
     instructions branch, requiring us to prove the goal for each possible destination.
     Fortunately, since this is a pretty simple invariant-set, the symbolic state
     inferred for all the goals trivially satisfies the theorem.  We can solve
     all by assumption or reflexivity: *)
  all: solve [ reflexivity | assumption ].
Qed.



(* Example #4: Partial correctness
   Finally, we can prove that strcmp returns the correct answer: EAX equals zero
   if the input strings are equal, EAX is negative if the first lexicographically
   precedes the second, and EAX is positive otherwise. *)

(* Define binary-level string equality: *)
Definition streq (m:addr->N) (p1 p2:addr) (k:N) :=
  ∀ i, i < k -> m Ⓑ[p1+i] = m Ⓑ[p2+i] /\ 0 < m Ⓑ[p1+i].

(* The post-condition says that interpreting EAX as a signed integer yields
   a number n whose sign equals the comparison of the kth byte in the two input
   strings, where the two strings are identical before k, and n may only be
   zero if the kth bytes are both nil. *)
Definition postcondition (m:addr->N) (esp:N) (s:store) :=
  ∃ n k, s R_EAX = Ⓓn /\
         streq m (m Ⓓ[4+esp]) (m Ⓓ[8+esp]) k /\
         (n=0 -> m Ⓑ[m Ⓓ[4+esp] + k] = 0) /\
         (m Ⓑ[m Ⓓ[4+esp] + k] ?= m Ⓑ[m Ⓓ[8+esp] + k]) = (toZ 32%N n ?= Z0)%Z.

(* The invariant-set for this property makes no assumptions at program-start
   (address 0), and puts a loop-invariant at address 8.  Putting a (trivial)
   invariant at the entry point 0 is optional, but it can make proofs easier
   because it will make the base case of your induction trivial to prove. *)
Definition strcmp_invs (m:addr->N) (esp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some True  (* no assumptions at entry point *)
  | 8 => Some (  (* loop invariant *)
     ∃ k, s R_ECX = Ⓓ(m Ⓓ[4+esp] ⊕ k) /\ s R_EDX = Ⓓ(m Ⓓ[8+esp] ⊕ k) /\
         streq m (m Ⓓ[4+esp]) (m Ⓓ[8+esp]) k
    )
  | 22 | 36 => Some (postcondition m esp s)
  | _ => None
  end | _ => None end.

(* Our partial correctness theorem makes the following assumptions:
   (ENTRY) Specify the start address and state of the subroutine.
   (MDL) Assume that on entry the processor is in a valid state.
   (ESP) Let esp be the value of the ESP register on entry.
   (MEM) Let mem be the memory state on entry.
   From these, we prove that all invariants (including the post-condition) hold
   true for arbitrarily long executions (i.e., arbitrary t). *)
Theorem strcmp_partial_correctness:
  forall s esp mem t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s)
         (ESP: s R_ESP = Ⓓesp) (MEM: s V_MEM32 = Ⓜmem),
  satisfies_all strcmp_i386 (strcmp_invs mem esp) strcmp_exit ((x',s')::t).
Proof.
  (* Start the proof the same way as before. *)
  intros. apply prove_invs.

  (* Prove the base case similarly. *)
  simpl. rewrite ENTRY. x86_step. exact I.

  (* Change assumptions about s into assumptions about s1. *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply strcmp_preserves_esp, satall_trueif_inv in ESP; try eassumption. simpl in ESP.
  erewrite strcmp_preserves_memory in MEM by eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strcmp_welltyped).
  assert (WTM := x86_wtm MDL MEM). simpl in WTM.
  clear - PRE ESP MEM MDL WTM. rename t1 into t. rename s1 into s.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x86_step.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 32 PRE.

  (* Address 0 *)
  step. step. exists 0. psimpl. split.
    reflexivity. split. reflexivity.
    intros i LT. destruct i; discriminate.

  (* Optional: The rest of the proof ignores all flag values except CF and ZF, so
     we can make evaluation faster and shorter by telling Picinae to ignore the
     other flags (i.e., abstract their values away). *)
  Ltac x86_ignore v ::= constr:(match v with
    R_AF | R_DF | R_OF | R_PF | R_SF => true
  | _ => false end).

  (* Address 8 *)
  destruct PRE as [k [ECX [EDX SEQ]]].
  step. step. step.

    (* Address 14 *)
    step. step. step. step.

      (* Address 20 *)
      step. apply Neqb_ok in BC.
      exists 0, k. psimpl. repeat first [ exact SEQ | split ].
        symmetry. apply Neqb_ok, BC0.
        apply N.compare_eq_iff, BC.

      (* loop back to Address 8 *)
      exists (k+1). psimpl. split. reflexivity. split. reflexivity.
      intros i IK. rewrite N.add_1_l in IK. apply N.lt_succ_r, N.le_lteq in IK. destruct IK as [IK|IK].
        apply SEQ, IK.
        subst. split.
          apply Neqb_ok in BC. assumption.
          apply N.neq_0_lt_0, N.neq_sym, N.eqb_neq. assumption.

    (* Address 23 *)
    step. step. step.
    eexists. exists k. psimpl. split. reflexivity. split. exact SEQ. split.
      intro. destruct (_ <? _); discriminate.
      apply N.eqb_neq, N.lt_gt_cases in BC. destruct BC as [BC|BC].
        rewrite (proj2 (N.compare_lt_iff _ _)), (proj2 (N.ltb_lt _ _)) by exact BC. reflexivity.
        rewrite (proj2 (N.compare_gt_iff _ _)) by exact BC. rewrite (proj2 (N.ltb_ge _ _)) by apply N.lt_le_incl, BC. reflexivity.
Qed.
