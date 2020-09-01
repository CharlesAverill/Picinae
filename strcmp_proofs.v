(* Example proofs using Picinae for Intel x86 Architecture

   Copyright (c) 2018 Kevin W. Hamlen
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
Proof. reflexivity. Qed. (* C:regular *)

(* CATEGORY: PICINAE lemmas *)
(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strcmp_welltyped: welltyped_prog x86typctx strcmp_i386.
Proof.
  Picinae_typecheck. (* C:picinae *)
Qed.

(* Example #2: Memory safety
   Strcmp contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem strlen_preserves_memory:
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|eassumption]. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.



(* Example #3: Architectural calling convention compliance
   Strcmp does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strcmp_preserves_ebx:
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' R_EBX = s R_EBX.
Proof.
  intros. eapply noassign_prog_same; [|eassumption]. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.

Theorem strcmp_preserves_readable:
  forall s n s' x,
  exec_prog fh strcmp_i386 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|eassumption]. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.

(* CATEGORY: memory safety *)
(* Proving that strlen restores ESP on exit is our first example of a property that
   requires stepwise symbolic interpretation of the program to verify.  We first
   define a set of invariants, one for each program point.  In this simple case,
   all program points have the same invariant, so we return the same one for all. *)
Definition esp_invs (esp:N) (_:addr) (s:store) := Some (s R_ESP = Ⓓ esp).

(* Next, we define the post-condition we wish to prove: *)
Definition esp_post (esp:N) (_:exit) (s:store) := s R_ESP = Ⓓ (esp ⊕ 4).

(* The invariant set and post-condition are combined into a single invariant-set
   using the "invs" function. *)
Definition strcmp_esp_invset esp :=
  invs (esp_invs esp) (esp_post esp).

(* Now we pose a theorem that asserts that this invariant-set is satisfied at
   all points in the subroutine.  The "trueif_inv" function asserts that
   anywhere an invariant exists (e.g., at the post-condition), it is true. *)
Theorem strcmp_preserves_esp:
  forall s esp mem n s' x'
         (ESP0: s R_ESP = Ⓓ esp) (MEM0: s V_MEM32 = Ⓜ mem)
         (RET: strcmp_i386 s (mem Ⓓ[esp]) = None)
         (XP0: exec_prog fh strcmp_i386 0 s n s' x'),
  trueif_inv (strcmp_esp_invset esp strcmp_i386 x' s').
Proof.
  intros. (* C:regular *)

  (* Use the prove_inv inductive principle from Picinae_theory.v. *)
  eapply prove_invs. exact XP0. (* C:picinae *)

  (* We must first prove the pre-condition, which says that the invariant-set is
     satisfied on entry to the subroutine.  This is proved by assumption ESP0. *)
  exact ESP0. (* C:picinae *)

  (* Now we enter the inductive case, wherein Coq asks us to prove that the invariant-set
     is preserved by every (reachable) instruction in the program.  Before breaking the
     goal down into many cases (one for each instruction in this case), it is wise to
     simplify and/or remove anything in the context that is unnecessary. In order for
     symbolic interpretation to succeed, the context must reveal the values of all
     relevant variables in store s1 (which denotes the store on entry to each instruction
     for which the goal must be proved).  The only two variables in our invariant-set are
     ESP and MEM.  The value of ESP will be revealed by our pre-condition (PRE).  We can
     get the value of MEM from MEM0 using our previously proved strlen_preserves_memory
     theorem. *)
  intros. (* C:picinae *)
  assert (MEM: s1 V_MEM32 = Ⓜ mem). (* C:picinae *)
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP. (* C:picinae *)
  rewrite (strcmp_nwc s1) in RET. (* C:picinae *)
  clear s MEM0 XP0 ESP0 XP. (* C:picinae *)

  (* We are now ready to break the goal down into one case for each invariant-point.
     The shelve_cases tactic finds all the invariants defined by the invariant-set
     in a precondition hypothesis (PRE).  Its first argument is the address bitwidth
     of the ISA (32 bits in this case).  After shelve_cases, use Coq's "Unshelve"
     command to recover the list of goals that the tactic "shelved" for you. *)
  shelve_cases 32 PRE. (* C:picinae *)
  Unshelve. (* C:picinae *)

  (* Now we launch the symbolic interpreter on all goals in parallel. *)
  all: x86_step. (* C:picinae *)

  (* Note that we wind up with more goals that we started with, since some of the
     instructions branch, requiring us to prove the goal for each possible destination.
     Fortunately, since this is a pretty simple invariant-set, the symbolic state
     inferred for all the goals trivially satisfies the theorem.  We can solve
     all by assumption or reflexivity: *)
  all: solve [ reflexivity | assumption ]. (* C:picinae *)
Qed.



(* CATEGORY: strcmp specification *)
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

(* CATEGORY: modular arithmetic lemma *)

Lemma lshift_lor_byte:
  forall n1 n2 w, ((n1 << w) .| n2) mod 2^w = n2 mod 2^w.
Proof.
  intros. (* C:regular *)
  rewrite <- (N.land_ones _ w), N.land_lor_distr_l, !(N.land_ones _ w). (* C:bitarith *)
  rewrite N.shiftl_mul_pow2, N.mod_mul by (apply N.pow_nonzero; discriminate). (* C:bitarith *)
  apply N.lor_0_l. (* C:bitarith *)
Qed.

(* CATEGORY: strcmp proof *)
(* Our partial correctness theorem makes the following assumptions:
   (MDL0) Assume that on entry the processor is in a valid state. *)
Theorem strcmp_partial_correctness:
  forall s esp mem n s' x
         (MDL0: models x86typctx s)
         (ESP0: s R_ESP = Ⓓ esp) (MEM0: s V_MEM32 = Ⓜ mem)
         (RET: strcmp_i386 s (mem Ⓓ[esp]) = None)
         (XP0: exec_prog fh strcmp_i386 0 s n s' x),
  trueif_inv (strcmp_invset mem esp strcmp_i386 x s').
Proof.
  intros. (* C:regular *)
  eapply prove_invs. exact XP0. (* C:picinae *)

  (* The pre-condition (True) is trivially satisfied. *)
  exact I. (* C:picinae *)

  (* Before splitting into cases, translate each hypothesis about the
     entry point store s to each instruction's starting store s1: *)
  intros. (* C:picinae *)
  assert (MDL: models x86typctx s1). (* C:picinae *)
    eapply preservation_exec_prog. exact MDL0. apply strcmp_welltyped. exact XP. (* C:picinae *)
  assert (MEM: s1 V_MEM32 = Ⓜ mem). (* C:picinae *)
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP. (* C:picinae *)
  assert (WTM := x86_wtm MDL MEM). simpl in WTM. (* C:picinae *)
  rewrite (strcmp_nwc s1) in RET. (* C:picinae *)
  assert (ESP := strcmp_preserves_esp _ _ _ _ _ (Exit a1) ESP0 MEM0 RET XP). (* C:picinae *)
  clear s MDL0 MEM0 ESP0 XP XP0. (* C:picinae *)

  (* Break the proof into cases, one for each invariant-point. *)
  shelve_cases 32 PRE. Unshelve. (* C:picinae *)

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x86_step. (* C:picinae *)

  (* Address 0 *)
  step. step. exists 0. (* C:picinae *)
  rewrite 2!N.add_0_r. rewrite !(N.mod_small (getmem _ _ _ _)) by apply getmem_bound, WTM. (* C:bitarith *)
  split. reflexivity. split. reflexivity. (* C:regular *)
  intros i LT. destruct i; discriminate. (* C:regular *)

  (* Address 8 *)
  destruct PRE as [k [ECX [EDX SEQ]]]. (* C:picinae *)
  step. step. (* C:picinae *)
    rewrite cmp_zf; [| apply N.mod_upper_bound, N.pow_nonzero; discriminate | apply WTM]. (* C:binarith *)
    rewrite lshift_lor_byte, (N.mod_small (mem _)) by apply WTM. (* C:binarith *)
  step. (* C:picinae *)

    (* Address 14 *)
    step. step. step. rewrite lshift_lor_byte, (N.mod_small (mem _)) by apply WTM. step. (* C:picinae *)

      (* Address 20 *)
      step. step. (* C:picinae *)
      exists 0, k. simpl_stores. repeat first [ exact SEQ | split ]. (* C:picinae *)
        intro. symmetry. apply Neqb_ok, BC0. (* C:regular *)
        apply N.compare_eq_iff, Neqb_ok, BC. (* C:regular *)

      (* loop back to Address 8 *)
      exists (k+1). rewrite !N.add_assoc, !N.add_mod_idemp_l by (apply N.pow_nonzero; discriminate). (* C:bitarith *)
      split. reflexivity. split. reflexivity. (* C:regular *)
      intros i IK. rewrite N.add_1_r in IK. apply N.lt_succ_r, N.le_lteq in IK. destruct IK as [IK|IK]. (* C:regular *)
        apply SEQ, IK. (* C:bitarith *)
        subst. split. (* C:regular *)
          apply Neqb_ok. assumption. (* C:regular *)
          apply N.neq_0_lt_0, N.neq_sym, N.eqb_neq. assumption. (* C:regular *)

    (* Address 23 *)
    step. step. step. step. (* C:picinae *)
    eexists. exists k. simpl_stores. split. reflexivity. split. exact SEQ. split. (* C:regular *)
      intro. destruct (_ <? _); discriminate. (* C:regular *)
      apply N.eqb_neq, N.lt_gt_cases in BC. destruct BC as [BC|BC]. (* C:regular *)
        rewrite (proj2 (N.compare_lt_iff _ _)), (proj2 (N.ltb_lt _ _)) by exact BC. reflexivity. (* C:regular *)
        rewrite (proj2 (N.compare_gt_iff _ _)) by exact BC. rewrite (proj2 (N.ltb_ge _ _)) by apply N.lt_le_incl, BC. reflexivity. (* C:regular *)
Qed.
(* CATEGORY: END *)
