(* Example proofs using Picinae for Intel x86 Architecture

   Copyright (c) 2022 Kevin W. Hamlen
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
Require Import strcmp_i386.

Import X86Notations.
Open Scope N.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

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
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.



(* Example #3: Architectural calling convention compliance
   Strcmp does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strcmp_preserves_ebx:
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' R_EBX = s R_EBX.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Theorem strcmp_preserves_readable:
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.


(* Proving that strlen restores ESP on exit is our first example of a property that
   requires stepwise symbolic interpretation of the program to verify.  We first
   define a set of invariants, one for each program point.  In this simple case,
   all program points have the same invariant, so we return the same one for all. *)
Definition esp_invs (esp0:N) (_:addr) (s:store) := Some (s R_ESP = Ⓓ esp0).

(* Next, we define the post-condition we wish to prove: *)
Definition esp_post (esp0:N) (_:exit) (s:store) := s R_ESP = Ⓓ (esp0 ⊕ 4).

(* The invariant set and post-condition are combined into a single invariant-set
   using the "invs" function. *)
Definition strcmp_esp_invset esp0 :=
  invs (esp_invs esp0) (esp_post esp0).

(* Now we pose a theorem that asserts that this invariant-set is satisfied at
   all points in the subroutine.  The "trueif_inv" function asserts that
   anywhere an invariant exists (e.g., at the post-condition), it is true. *)
Theorem strcmp_preserves_esp:
  forall s esp0 mem n s' x'
         (MDL0: models x86typctx s)
         (ESP0: s R_ESP = Ⓓ esp0) (MEM0: s V_MEM32 = Ⓜ mem)
         (RET: strcmp_i386 s (mem Ⓓ[esp0]) = None)
         (XP0: exec_prog fh strcmp_i386 0 s n s' x'),
  trueif_inv (strcmp_esp_invset esp0 strcmp_i386 x' s').
Proof.
  intros.

  (* Use the prove_invs inductive principle from Picinae_theory.v. *)
  eapply prove_invs. exact XP0.

  (* We must first prove the pre-condition, which says that the invariant-set is
     satisfied on entry to the subroutine.  This is proved by assumption ESP0. *)
  exact ESP0.

  (* Now we enter the inductive case, wherein Coq asks us to prove that the invariant-set
     is preserved by every (reachable) instruction in the program.  Before breaking the
     goal down into many cases (one for each instruction in this case), it is wise to
     simplify and/or remove anything in the context that is unnecessary. In order for
     symbolic interpretation to succeed, the proof context must reveal the values of all
     relevant variables in store s1 (which denotes the store on entry to each instruction
     for which the goal must be proved).  The only two variables in our invariant-set are
     ESP and MEM.  The value of ESP is already revealed by pre-condition (PRE), and we
     can get the value of MEM from MEM0 using our previously proved strlen_preserves_memory
     theorem. *)
  intros.
  assert (MDL: models x86typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strcmp_welltyped. exact XP.
  assert (MEM: s1 V_MEM32 = Ⓜ mem).
    rewrite <- MEM0. eapply strcmp_preserves_memory. exact XP.
  rewrite (strcmp_nwc s1) in RET.
  clear s MDL0 MEM0 XP0 ESP0 XP.

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

(* Define string equality: *)
Definition streq (m:addr->N) (p1 p2:addr) (k:N) :=
  ∀ i, i < k -> m (p1⊕i) = m (p2⊕i) /\ 0 < m (p1⊕i).

(* The invariant-set for this property makes no assumptions at program-start
   (address 0), and puts a loop-invariant at address 8. *)
Definition strcmp_invs (m:addr->N) (esp:N) (a:addr) (s:store) :=
  match a with
  |  0 => Some True
  |  8 => Some (∃ k, s R_ECX = Ⓓ(m Ⓓ[esp⊕4] ⊕ k) /\ s R_EDX = Ⓓ(m Ⓓ[esp⊕8] ⊕ k) /\
                streq m (m Ⓓ[esp⊕4]) (m Ⓓ[esp⊕8]) k)
  | _ => None
  end.

(* The post-condition says that interpreting EAX as a signed integer yields
   a number n whose sign equals the comparison of the kth byte in the two input
   strings, where the two strings are identical before k, and n may only be
   zero if the kth bytes are both nil. *)
Definition strcmp_post (m:addr->N) (esp:N) (_:exit) (s:store) :=
  ∃ n k, s R_EAX = Ⓓn /\
         streq m (m Ⓓ[esp⊕4]) (m Ⓓ[esp⊕8]) k /\
         (n=0 -> m (m Ⓓ[esp⊕4] ⊕ k) = 0) /\
         (m (m Ⓓ[esp⊕4] ⊕ k) ?= m (m Ⓓ[esp⊕8] ⊕ k)) = (toZ 32 n ?= Z0)%Z.

(* The invariant-set and post-conditions are combined as usual: *)
Definition strcmp_invset (mem:addr->N) (esp:N) :=
  invs (strcmp_invs mem esp) (strcmp_post mem esp).

Lemma lshift_lor_byte:
  forall n1 n2 w, ((n1 << w) .| n2) mod 2^w = n2 mod 2^w.
Proof.
  intros.
  rewrite <- (N.land_ones _ w), N.land_lor_distr_l, !(N.land_ones _ w).
  rewrite N.shiftl_mul_pow2, N.mod_mul by (apply N.pow_nonzero; discriminate).
  apply N.lor_0_l.
Qed.

(* Our partial correctness theorem makes the following assumptions:
   (MDL0) Assume that on entry the processor is in a valid state.
   (ESP0) Let esp be the value of the ESP register on entry.
   (MEM0) Let mem be the memory state on entry.
   (RET) Assume the return address on the stack on entry is not within strcmp(!)
   (XP0) Let x and s' be the exit condition and store after n instructions execute.
   From these, we prove that all invariants (including the post-condition) hold
   true for arbitrarily long executions (i.e., arbitrary n). *)
Theorem strcmp_partial_correctness:
  forall s esp mem n s' x
         (MDL0: models x86typctx s)
         (ESP0: s R_ESP = Ⓓ esp) (MEM0: s V_MEM32 = Ⓜ mem)
         (RET: strcmp_i386 s (mem Ⓓ[esp]) = None)
         (XP0: exec_prog fh strcmp_i386 0 s n s' x),
  trueif_inv (strcmp_invset mem esp strcmp_i386 x s').
Proof.
  intros.
  eapply prove_invs. exact XP0.

  (* The pre-condition (True) is trivially satisfied. *)
  exact I.

  (* Before splitting into cases, translate each hypothesis about the
     entry point store s to each instruction's starting store s1: *)
  intros.
  assert (MDL: models x86typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strcmp_welltyped. exact XP.
  assert (MEM: s1 V_MEM32 = Ⓜ mem).
    rewrite <- MEM0. eapply strcmp_preserves_memory. exact XP.
  assert (WTM := x86_wtm MDL MEM). simpl in WTM.
  rewrite (strcmp_nwc s1) in RET.
  assert (ESP := strcmp_preserves_esp _ _ _ _ _ (Exit a1) MDL0 ESP0 MEM0 RET XP).
  clear s MDL0 MEM0 ESP0 XP XP0.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 32 PRE.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x86_step.

  (* Address 0 *)
  step. step. exists 0.
  rewrite 2!N.add_0_r. rewrite !(N.mod_small (getmem _ _ _ _)) by apply getmem_bound, WTM.
  split. reflexivity. split. reflexivity.
  intros i LT. destruct i; discriminate.

  (* Address 8 *)
  destruct PRE as [k [ECX [EDX SEQ]]].
  step. step. step.

    (* Address 14 *)
    step. step. step. step.

      (* Address 20 *)
      step. step.
      exists 0, k. psimpl. repeat first [ exact SEQ | split ].
        intro. symmetry. apply Neqb_ok, BC0.
        apply N.compare_eq_iff, Neqb_ok, BC.

      (* loop back to Address 8 *)
      exists (k+1). rewrite !N.add_assoc.
      split. reflexivity. split. reflexivity.
      intros i IK. rewrite N.add_1_r in IK. apply N.lt_succ_r, N.le_lteq in IK. destruct IK as [IK|IK].
        apply SEQ, IK.
        subst. split.
          apply Neqb_ok. assumption.
          apply N.neq_0_lt_0, N.neq_sym, N.eqb_neq. assumption.

    (* Address 23 *)
    step. step. step. step.
    eexists. exists k. psimpl. split. reflexivity. split. exact SEQ. split.
      intro. destruct (_ <? _); discriminate.
      apply N.eqb_neq, N.lt_gt_cases in BC. destruct BC as [BC|BC].
        rewrite (proj2 (N.compare_lt_iff _ _)), (proj2 (N.ltb_lt _ _)) by exact BC. reflexivity.
        rewrite (proj2 (N.compare_gt_iff _ _)) by exact BC. rewrite (proj2 (N.ltb_ge _ _)) by apply N.lt_le_incl, BC. reflexivity.
Qed.
