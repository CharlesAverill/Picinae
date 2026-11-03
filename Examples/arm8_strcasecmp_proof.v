(* Example proof of correctness for an ARM8 implementation of strcasecmp,
   including subroutine tolower.  This demonstrates multi-subroutine
   code verification in Picinae.

   Credit: Proved by Kevin Hamlen while developing Picinae's multi-
     subroutine support logic, loosely based on an earlier attempt by
     students Nathaniel Simmons, Aaron Hill, Long Nguyen, Ariz Siddiqui.
 *)

From Stdlib Require Import Utf8.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.
Require Import Picinae_armv8.
Require Import arm8_strcasecmp.

Import ARM8Notations.
Open Scope N.
Open Scope bool.

(* The ARMv8 lifter models non-writable code. *)
Theorem strcasecmp_nwc:
	forall s2 s1, strcasecmp s1 = strcasecmp s2.
Proof.
	reflexivity.
Qed.

(* The ARMv8 lifter produces well-typed IL. *)
Theorem strcasecmp_welltyped:
	welltyped_prog arm8typctx strcasecmp.
Proof.
  Picinae_typecheck.
Qed.

(* Define binary string case-insensitivity. *)
Definition tolower (c:N) : N :=
  if (65 <=? c mod 2^32) && (c mod 2^32 <=? 90) then (c mod 2^32 .| 32) else c.

(* Define binary length-bounded, case-insensitive string equality. *)
Definition strcaseeq (m:memory) (p1 p2: addr) (k: N) :=
  ∀ i, i < k -> tolower (m Ⓑ[p1+i]) = tolower (m Ⓑ[p2+i]) /\ 0 < m Ⓑ[p1+i].

Section Invariants.

  Variable sp : N          (* initial stack pointer *).
  Variable mem : memory    (* initial memory state *).
  Variable raddr : N       (* return address (R_X30) *).
  Variable arg1 : N        (* strcasecmp: 1st pointer arg (R_X0)
                              tolower: input character (R_X0) *).
  Variable arg2 : N        (* strcasecmp: 2nd pointer arg (R_X1)
                              tolower: callee-save reg (R_X19) *).
  Variable x20 x21 : N     (* tolower: R_X20, R_X21 (callee-save regs) *).

  Definition mem' fbytes := setmem 64 LittleE 40 mem (sp ⊖ 48) fbytes.

  (* The post-condition says that interpreting x0 as a signed integer z
     whose sign equals the comparison of the kth byte in the two input
     strings, where the two strings are identical before k, and z may only be
     zero if the kth bytes are both nil. *)
  Definition postcondition (s:store) :=
    ∃ n k fb,
      s V_MEM64 = mem' fb /\
      s R_X0 = n /\
      strcaseeq (mem' fb) arg1 arg2 k /\
      (n=0 -> (mem' fb) Ⓑ[arg1+k] = 0) /\
      (tolower (mem' fb Ⓑ[arg1+k]) ?= tolower(mem' fb Ⓑ[arg2+k])) = (toZ 32%N n ?= Z0)%Z.

  (* Invariant sets f for multi-subroutine properties have the following signature:
        f (T:Type) (Invs Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T
     where inv_type T = N -> Prop -> T.  They thereby map addresses a:addr to
     internal invariants (Invs n P), post-conditions (Post n P), or no-invariant (NoInv),
     where n:N is a subroutine identifier number and P:Prop is the invariant.
     Polymorphic parameters Invs, Post, and NoInv act like constructors of return type T.
     Property P usually references store s, and is therefore a property of s.
     Identifiers n are unique to each subroutine in the code, and establish a
     partial order over subroutines:  A caller with identifier m may use Picinae's
     perform_call theorem to call a callee with identifier n whenever m > n.
     (To verify mutually recursive nests of subroutines, they must be assigned a
     common identifier and verified as a single recursive subroutine.)

     Note that because of the "Variable" declarations above, the following invariant
     set definition "invs" actually has extra initial hidden parameters, one for each
     sectional Variable it references:
       invs sp mem raddr ... T Inv Post NoInv s a
     It therefore actually defines an invariant set family, one invariant set for each
     possible instantiation of the Variable parameters before T.  To allow a caller to
     call a callee with a different invariant set from the same family using perform_call,
     the two invariant sets f and g must satisfy (same_invset_family f g), which stipulates
     that f and g agree on whether an internal invariant or post-condition exists at each
     address, though they may differ on what the invariant P is.  The same_invset_family
     obligation is provable by reflexivity as long as your definition only refers to
     (hidden) parameters before T within the P arguments of Inv and Post. *)
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcasecmp entry point *)
    | 1048576 => Inv 1 (
        s R_SP = sp /\ s V_MEM64 = mem /\
        s R_X0 = arg1 /\ s R_X1 = arg2
      )

    (* loop invariant *)
    | 1048600 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\
        s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
        s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k
      )

    (* case-equal, non-null characters found *)
    | 1048688 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\
        s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
        s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k /\
        (tolower(mem' fb Ⓑ[arg1 + k]) = tolower(mem' fb Ⓑ[arg2 + k])) /\
        mem' fb Ⓑ[arg1 + k] ≠ 0
      )

    (* case-unequal or null characters found *)
    | 1048648 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\ (*characters before k matched*)
        s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
        s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k /\
          (tolower(mem' fb Ⓑ[arg1 + k]) ≠ tolower(mem' fb Ⓑ[arg2 + k]) \/
           mem' fb Ⓑ[arg1 + k] = 0)
      )

    (* strcasecmp return site *)
    | 1048684 => Post 1 (postcondition s)

    (* tolower entry point *)
    | 2097152 => Inv 0 (s R_X0 = arg1 /\ s R_X19 = arg2 /\
         s R_X20 = x20 /\ s R_X21 = x21 /\
         s R_X30 = raddr /\ s R_SP = sp /\ s V_MEM64 = mem)

    (* tolower return point *)
    | 2097168 => Post 0 (s R_X0 = tolower arg1 /\ s R_X19 = arg2 /\
         s R_X20 = x20 /\ s R_X21 = x21 /\
         s R_X30 = raddr /\ s R_SP = sp /\ s V_MEM64 = mem)

    | _ => NoInv
    end.

  (* Picinae's helper functions make_exits and make_invs are next leveraged to
     define appropriate invariant sets for each subroutine by extracting them
     from the above.  Note that these definitions receive the same extra hidden
     parameters as invs above, so are actually invariant set families. *)
  Definition exits0 := make_exits 0 strcasecmp invs.
  Definition invs0 := make_invs 0 strcasecmp invs.
  Definition exits1 := make_exits 1 strcasecmp invs.
  Definition invs1 := make_invs 1 strcasecmp invs.

End Invariants.


(* Prove a few helper lemmas about tolower and friends: *)

Lemma tolower_small:
  forall w e m a, tolower (getmem w e 1 m a) < 2^8.
Proof.
  intros. unfold tolower. destruct (andb _ _).
    apply lor_bound.
      rewrite <- getmem_mod_r, mp2_mod_mod_min. apply mp2_mod_lt.
      reflexivity.
    apply getmem_bound.
Qed.

Lemma tolower_mod:
  forall c, (tolower c) mod 2^32 = tolower (c mod 2^32).
Proof.
  intro. unfold tolower. rewrite mp2_mod_mod. destruct (andb _ _).
    rewrite <- N.land_ones, N.land_lor_distr_l, N.land_ones, mp2_mod_mod. reflexivity.
    reflexivity.
Qed.

Lemma tolower_byte:
  forall w e m a, (tolower (getmem w e 1 m a)) mod 2^32 =
                  tolower (getmem w e 1 m a).
Proof.
  intros. rewrite tolower_mod, N.mod_small. reflexivity.
  etransitivity. apply getmem_bound. reflexivity.
Qed.

Lemma tolower_test:
  forall c,
    (if 25 <=? msub 32 c 65
     then if c mod 2^32 =? 90 then 0 else 1
     else 0) =
    (if andb (65 <=? c mod 2^32) (c mod 2^32 <=? 90) then 0 else 1).
Proof.
  intro c. destruct (N.eq_dec (c mod 2^32) 90) as [H1|H1].
    rewrite <- (msub_mod_l 32 32). rewrite H1. reflexivity. reflexivity.
    rewrite (proj2 (N.eqb_neq _ _) H1). destruct (65 <=? _) eqn:H2.
      apply N.leb_le in H2. destruct (_ <=? 90) eqn:H3.
        rewrite (proj2 (N.leb_gt _ _)).
          reflexivity.
          change 25 with (msub 32 90 65). apply msub_lt_mono_r.
            left. rewrite N.min_l. apply H2. apply N.leb_le, H3.
            apply N.leb_le, N.le_lteq in H3. destruct H3 as [H3|H3].
              assumption.
              contradict H1. assumption.
        apply N.leb_gt in H3. rewrite msub_nowrap by assumption. rewrite (proj2 (N.leb_le _ _)).
          reflexivity.
          apply N.le_add_le_sub_l, N.lt_le_incl, H3.
      rewrite msub_wrap by apply N.leb_gt, H2. rewrite (proj2 (N.leb_le _ _)).
        reflexivity.
        apply N.le_add_le_sub_l. transitivity (2^32). discriminate 1. apply N.le_add_r.
Qed.

Lemma diff_compare:
  forall m n (H1: m < 2^8) (H2: n < 2^8),
    (m ?= n) = (toZ 32%N (msub 32%N m n) ?= 0)%Z.
Proof.
  intros.
  assert (H1': m < 2^32). eapply N.lt_le_trans. apply H1. discriminate.
  assert (H2': n < 2^32). eapply N.lt_le_trans. apply H2. discriminate.
  destruct (m ?= n) eqn:H3; symmetry.
    apply N.compare_eq_iff in H3. subst. rewrite msub_diag. reflexivity.
    apply (proj2 (Z.compare_lt_iff _ _)), Z.lt_nge.
      intro H. apply toZ_sign in H. revert H. apply N.le_ngt.
      rewrite msub_mod_pow2, N.min_id. apply le_msub_iff.
      right. rewrite !N.mod_small by assumption. split.
        apply (proj1 (N.compare_lt_iff _ _) H3).
        transitivity (2^8+2^31).
          apply N.add_le_mono. apply N.lt_le_incl, H2. discriminate.
          transitivity (2^32). discriminate. apply N.le_add_r.
    apply (proj1 (N.compare_gt_iff _ _)) in H3. apply (proj2 (Z.compare_gt_iff _ _)).
      rewrite msub_nowrap by (rewrite !N.mod_small by assumption; apply N.lt_le_incl, H3).
      rewrite !N.mod_small by assumption.
      rewrite (proj1 (toZ_nonneg _ _)); rewrite N.mod_small.
      rewrite N2Z.inj_sub by apply N.lt_le_incl, H3. apply Z.lt_0_sub, N2Z.inj_lt, H3.
      1-3: eapply N.le_lt_trans; [apply N.le_sub_l|try assumption].
      eapply N.lt_le_trans. apply H1. discriminate.
Qed.

(* Create a step tactic that prints a progress message (for demos). *)
Ltac step := time arm8_step.

(* Prove that each subroutine satisfies the invariant set, starting with callees
   and proceeding to callers.  In this case, we start with subroutine tolower: *)
Theorem tolower_correctness:
  forall s sp mem t xs' arg1 arg2 a'
         (ENTRY: startof t xs' = (Addr 2097152, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = sp) (MEM: s V_MEM64 = mem)
         (X0: s R_X0 = arg1) (X19: s R_X19 = arg2)
         (X30: s R_X30 = a'),
  satisfies_all strcasecmp (invs0  sp mem a' arg1 arg2 (s R_X20) (s R_X21))
                           (exits0 sp mem a' arg1 arg2 (s R_X20) (s R_X21)) (xs'::t).
Proof.
  (* Use prove_invs to initiate a proof by induction. *)
  intros. apply prove_invs.

  (* Base case: The invariant at the subroutine entry point is satisfied. *)
  simpl. rewrite ENTRY. step. repeat split; assumption.

  (* Before proving all the inductive cases (which each start at an internal
     invariant point), clean up the proof context by replacing any hypotheses
     about initial cpu state s with equivalent hypotheses about the cpu state s1
     that appears at the invariant point at which we're starting this case. *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasecmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.

  (* Break the proof into cases, one for each internal invariant-point. *)
  destruct_inv 64 PRE.

  (* Address 152 (tolower entry point) *)
  destruct PRE as (X0 & X19 & X20 & X21 & X30 & SP & MEM).
  step. step. step.

    (* Address 1048164 *)
    step. repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). reflexivity. discriminate.

    (* Address 104168 *)
    repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). discriminate. reflexivity.
Qed.

(* Now prove correctness of the main strcasecmp subroutine,
   using our earlier proof of tolower at subroutine calls. *)
Theorem strcmp_partial_correctness:
  forall s sp mem t s' x' arg1 arg2 a'
         (ENTRY: startof t (x',s') = (Addr 1048576, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = a')
         (RX0: s R_X0 = arg1) (RX1: s R_X1 = arg2),
  satisfies_all strcasecmp (invs1  sp mem a' arg1 arg2 (s R_X20) (s R_X21))
                           (exits1 sp mem a' arg1 arg2 (s R_X20) (s R_X21)) ((x',s')::t).
Proof.
  (* Use prove_invs to initiate a proof by induction. *)
  intros. apply prove_invs.

  (* Base case: The invariant at the subroutine entry point is satisfied. *)
  simpl. rewrite ENTRY. step. repeat split; assumption.

  (* Change assumptions about s into assumptions about s1. *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasecmp_welltyped. intro MDL1.
  set (x20 := s R_X20) in *. set (x21 := s R_X21) in *. clearbody x20 x21.
  clear - PRE MDL1. rename t1 into t. rename s1 into s. rename MDL1 into MDL.

  (* Break the proof into cases, one for each internal invariant-point. *)
  destruct_inv 64 PRE.

  (* Address 1048576: strcasecmp entry point *)
  destruct PRE as (MEM & SP & X0 & X1).
  step. step. step. step. step. step.
  generalize_frame mem as fb.
  exists fb, 0. psimpl. split.
    intros i LT. destruct i; discriminate.
    repeat split.

  (* Address 1048600: strcasecmp main loop *)
  destruct PRE as (fb & k & SEQ & SP & MEM & X19 & X20).
  step. step.

    (* Address 1048648: reached null terminator in arg1 *)
    exists fb, k. repeat (reflexivity || assumption || split).
    right. apply N.eqb_eq, BC.

    (* Address 1048608: character in arg1 is non-null. *)
    apply N.eqb_neq in BC.
    step. step.

      (* Address 1048648: reached null terminator in arg2 *)
      apply N.eqb_eq in BC0.
      exists fb, k. repeat (reflexivity || assumption || split).
      left. rewrite BC0. change (tolower 0) with 0. unfold tolower.
      destruct (andb _ _).
        intro H. apply N.lor_eq_0_iff, proj2 in H. discriminate.
        assumption.

      (* Address 1048616: Current char in both strings are non-null. *)
      apply N.eqb_neq in BC0.
      step. step.

        (* Address 1048688: identical characters found *)
        eexists fb, k. repeat (assumption || reflexivity || split).
        apply N.eqb_eq in BC1. rewrite BC1. reflexivity.

        (* Address 1048624: Unequal characters found. Call tolower(arg1). *)
        step.
        set (s1 := update _ _ _).
        eapply models_after_steps. eassumption. apply strcasecmp_welltyped. intro MDL1.
        eapply (perform_call 0). reflexivity.
        intros. eapply tolower_correctness; (eassumption || reflexivity).
        reflexivity.

        (* Clean up the proof context after the call by creating hypotheses
           about the post-call cpu state s1 and discarding hypotheses about
           old cpu states. *)
        intros.
        unfold s1 in PRE. psimpl in PRE.
        assert (MDL': models arm8typctx s').
          eapply preservation_exec_prog; try eassumption.
          apply strcasecmp_welltyped.
        set (t' := t2++t0++_::t) in *. clearbody s1 t'.
        set (x21' := s R_X21) in PRE. clearbody x21'.
        clear - SEQ BC BC0 BC1 PRE MDL'.
        rename MDL' into MDL. rename t' into t. rename a'0 into a. rename s' into s.

        (* Separate the proof into one subgoal for each subroutine exit point.
           (In the case of tolower, there's only one exit point. *)
        destruct_inv 64 PRE.

        destruct PRE as (X0 & X19 & X20 & X21 & X30 & SP & MEM).
        clear X21 x21'. (* This particular call site ignores x21, so delete it. *)
        step. step. step. step.

        (* Another call to tolower, performed in the same way as above. *)
        set (s1 := update _ _ _).
        eapply models_after_steps. eassumption. apply strcasecmp_welltyped. intro MDL1.
        eapply (perform_call 0). reflexivity.
        intros. eapply tolower_correctness; (eassumption || reflexivity).
        reflexivity.

        intros.
        unfold s1 in PRE. psimpl in PRE.
        assert (MDL': models arm8typctx s').
          eapply preservation_exec_prog; try eassumption.
          apply strcasecmp_welltyped.
        set (t' := t2++t0++_::t) in *. clearbody s1 t'.
        rewrite X20 in PRE.
        clear - SEQ BC BC0 BC1 PRE MDL'.
        rename MDL' into MDL. rename t' into t. rename a'0 into a. rename s' into s.

        destruct_inv 64 PRE.

        destruct PRE as (X0 & X19 & X20 & X21 & X30 & SP & MEM).
        step. step. step.

          (* Address 1048688: found case-equal characters *)
          exists fb, k.
          rewrite !tolower_byte in BC2.
          repeat first [ assumption | split ].
          apply N.eqb_eq, BC2.

          (* Address 1048648: found case-unequal characters *)
          exists fb, k.
          rewrite !tolower_byte in BC2.
          repeat first [ assumption | split ].
          left. apply N.eqb_neq, BC2.

        (* Address 1048648: case-unequal chars or null found *)
        destruct PRE as (fb & k & SEQ & SP & MEM & X19 & X20 & NEQ).
        step. step.

        (* Another call to tolower, performed the same as above. *)
        set (s1 := update _ _ _).
        eapply models_after_steps. eassumption. apply strcasecmp_welltyped. intro MDL1.
        eapply (perform_call 0). reflexivity.
        intros. eapply tolower_correctness; (eassumption || reflexivity).
        reflexivity.

        intros.
        unfold s1 in PRE. psimpl in PRE.
        set (x21' := s R_X21) in PRE. clearbody x21'.
        assert (MDL': models arm8typctx s').
          eapply preservation_exec_prog; try eassumption.
          apply strcasecmp_welltyped.
        set (t' := t2++t0++_::t) in *. clearbody s1 t'.
        clear - SEQ NEQ PRE MDL'.
        rename MDL' into MDL. rename t' into t. rename a'0 into a. rename s' into s.

        destruct_inv 64 PRE.

        destruct PRE as (X0 & X19 & X20 & X21 & X30 & SP & MEM).
        clear X21 x21'.
        step. step. step. step.

        (* Another call to tolower, performed the same as above. *)
        set (s1 := update _ _ _).
        eapply models_after_steps. eassumption. apply strcasecmp_welltyped. intro MDL1.
        eapply (perform_call 0). reflexivity.
        intros. eapply tolower_correctness; (eassumption || reflexivity).
        reflexivity.

        intros.
        unfold s1 in PRE. psimpl in PRE.
        set (x21' := s R_X21) in PRE. clearbody x21'.
        assert (MDL': models arm8typctx s').
          eapply preservation_exec_prog; try eassumption.
          apply strcasecmp_welltyped.
        set (t' := t2++t0++_::t) in *. clearbody s1 t'.
        clear - SEQ NEQ PRE MDL'.
        rename MDL' into MDL. rename t' into t. rename a'0 into a. rename s' into s.

        destruct_inv 64 PRE.

        destruct PRE as (X0 & X19 & X20 & X21 & X30 & SP & MEM).
        clear X21 x21'.
        step. step. step. step. step.
        eexists _, k, fb. repeat first [ reflexivity | assumption | split ].
          intro H. apply msub_move_0_r in H. destruct NEQ as [H'|H'].
            contradict H'. rewrite !tolower_byte in H. assumption.
            assumption.
          apply diff_compare; apply tolower_small.

  (* Address 1048688: case-equal, non-nil chars found (loop back) *)
  destruct PRE as (fb & k & SEQ & SP & MEM & X19 & X20 & EQ & NN).
  step. step. step.
  exists fb, (k+1). split.
    rewrite N.add_1_r. intros i H. apply N.lt_succ_r, N.le_lteq in H. destruct H.
      revert i H. apply SEQ.
      subst i. split. assumption. apply N.neq_0_lt_0, NN.
    psimpl. repeat split; assumption.
Qed. (* <-- This Qed might take a few minutes depending on your machine. *)
(* The callee contains no loops or memory accesses. The exit is its return
   instruction, as in tolower_correctness; execution of the caller follows. *)
Theorem tolower_total_correctness:
  forall s sp mem arg1 arg2 a'
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem)
    (X0: s R_X0 = arg1) (X19: s R_X19 = arg2)
    (X30: s R_X30 = a'),
  satisfies_total strcasecmp
    (invs0 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
    (exits0 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
    ((Addr 2097152,s)::nil).
Proof.
  intros. unfold satisfies_total.
  do 3 ISA_total_step.
    ISA_total_step. total_here.
    cbn [invs0 exits0 make_exits make_invs invs strcasecmp true_inv].
    psimpl. repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). reflexivity. discriminate.
    total_here.
    cbn [invs0 exits0 make_exits make_invs invs strcasecmp true_inv].
    psimpl. repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). discriminate. reflexivity.
Qed.

Print Assumptions tolower_total_correctness.

(* Total correctness of the main routine.  The partial proofs above are reused
   unchanged for the functional invariant at the original exit. *)
From Stdlib Require Import List Lia.

(* Full permissions are a simple sufficient memory-safety condition.  The
   bound matters: ARM8 permission maps have exactly 2^64 bits. *)
Definition strcasecmp_readable (s:store) :=
  forall a, a < 2^64 -> mem_readable s a.
Definition strcasecmp_writable (s:store) :=
  forall a, a < 2^64 -> mem_writable s a.

Ltac total_memory ::=
  intros; unfold mem_readable, mem_writable;
  psimpl; first
    [match goal with H: strcasecmp_readable _ |- _ => apply H end
    |match goal with H: strcasecmp_writable _ |- _ => apply H end];
  apply mp2_mod_lt.

(* Inline finite callee execution, including the return instruction.  Unlike
   the callee's public theorem, this helper retains an arbitrary caller history
   and resumes at its saved return address. *)
Lemma strcasecmp_tolower_returns:
  forall (Q:trace -> Prop) s t ret (RET: s R_X30 = ret)
    (CONT: forall s' t',
      s' R_X20 = s R_X20 -> s' V_MEM64 = s V_MEM64 ->
      s' A_READ = s A_READ ->
      eventually strcasecmp Q ((Addr ret,s')::t')),
  eventually strcasecmp Q ((Addr 2097152,s)::t).
Proof.
  intros. do 3 ISA_total_step.
    do 2 ISA_total_step. apply CONT; reflexivity.
    ISA_total_step. apply CONT; reflexivity.
Qed.

(* Restrict an eventual exit to the first exit, retaining the execution facts
   required by the original partial-correctness theorem. *)
Lemma strcasecmp_first_exit:
  forall p xp entry t,
  eventually p (fun t' => xp t' = true) t ->
  execution_context p xp entry t ->
  eventually p (fun t' => xp t' = true /\
    execution_context p xp entry t') t.
Proof.
  intros p xp entry t EV. induction EV; intro CTX.
  - total_here. split; assumption.
  - destruct (xp (xs::t)) eqn:EX.
    + total_here. split; assumption.
    + destruct CTX as (XP & ORIGIN & UT).
      eapply EventuallyStep. exact ENABLED.
      intros xs' CS. apply H; [exact CS|].
      split. apply exec_prog_step; assumption.
      split. rewrite ostartof_step. exact ORIGIN.
      simpl. apply unterminated_cons; assumption.
Qed.

Definition strcasecmp_at_return (t:trace) :=
  match t with (Addr a,_)::_ => a = 1048684 | _ => False end.

(* The exit path has two finite calls and then restores the saved registers. *)
Lemma strcasecmp_finish:
  forall s t (READ: strcasecmp_readable s),
  eventually strcasecmp strcasecmp_at_return ((Addr 1048648,s)::t).
Proof.
  intros. do 2 ISA_total_step.
  eapply strcasecmp_tolower_returns; [reflexivity|].
  intros scallee1 t1 X20 MEM RP.
  assert (READ1: strcasecmp_readable scallee1).
    unfold strcasecmp_readable, mem_readable in *. rewrite RP. exact READ.
  clear READ. rename READ1 into READ.
  do 3 ISA_total_step.
  eapply strcasecmp_tolower_returns; [reflexivity|].
  intros scallee2 t2 X20' MEM' RP'.
  assert (READ2: strcasecmp_readable scallee2).
    unfold strcasecmp_readable, mem_readable in *. rewrite RP'. exact READ.
  clear READ. rename READ2 into READ.
  do 4 ISA_total_step.
  total_here. reflexivity.
Qed.

(* The loop-back block performs two modular pointer increments. *)
Lemma strcasecmp_advance:
  forall (Q:trace -> Prop) s t
    (CONT: forall s' t',
      s' R_X20 = s R_X20 ⊕ 1 -> s' V_MEM64 = s V_MEM64 ->
      s' A_READ = s A_READ ->
      eventually strcasecmp Q ((Addr 1048600,s')::t')),
  eventually strcasecmp Q ((Addr 1048688,s)::t).
Proof.
 intros. do 3 ISA_total_step. apply CONT; psimpl; reflexivity.
Qed.

(* The remaining distance to a null byte decreases on every loop iteration.
   Addresses and the distance are modular, so this also admits wrapping strings.
   A mismatch or an earlier null in either input takes the finite exit path. *)
Lemma strcasecmp_loop_terminates:
  forall n s t (READ: strcasecmp_readable s)
    (NULL: (s V_MEM64) Ⓑ[s R_X20 + n] = 0),
  eventually strcasecmp strcasecmp_at_return ((Addr 1048600,s)::t).
Proof.
  induction n using N.peano_ind; intros.
  - rewrite N.add_0_r in NULL.
    do 2 ISA_total_step.
      apply strcasecmp_finish. unfold strcasecmp_readable, mem_readable in *.
      psimpl. exact READ.
      rewrite NULL in BC. discriminate.
  - do 2 ISA_total_step.
      apply strcasecmp_finish. unfold strcasecmp_readable, mem_readable in *.
      psimpl. exact READ.
    do 2 ISA_total_step.
      apply strcasecmp_finish. unfold strcasecmp_readable, mem_readable in *.
      psimpl. exact READ.
    do 2 ISA_total_step.
    + eapply strcasecmp_advance. intros sadv hist XADV MADV RADV.
      apply IHn.
        unfold strcasecmp_readable, mem_readable in *. rewrite RADV. exact READ.
        rewrite XADV, MADV. psimpl. psimpl in NULL.
        rewrite N.add_1_l, N.add_succ_l, <- N.add_succ_r.
        exact NULL.
    + ISA_total_step.
      eapply strcasecmp_tolower_returns; [reflexivity|].
      intros scallee1 t1 X20 MEM RP.
      assert (READ1: strcasecmp_readable scallee1).
        unfold strcasecmp_readable, mem_readable in *. rewrite RP. exact READ.
      assert (NULL1: (scallee1 V_MEM64) Ⓑ[scallee1 R_X20 + N.succ n] = 0).
        rewrite X20, MEM. psimpl. psimpl in NULL. exact NULL.
      clear - IHn READ1 NULL1. rename READ1 into READ. rename NULL1 into NULL.
      do 3 ISA_total_step.
      eapply strcasecmp_tolower_returns; [reflexivity|].
      intros scallee2 t2 X20' MEM' RP'.
      assert (READ2: strcasecmp_readable scallee2).
        unfold strcasecmp_readable, mem_readable in *. rewrite RP'. exact READ.
      assert (NULL2: (scallee2 V_MEM64) Ⓑ[scallee2 R_X20 + N.succ n] = 0).
        rewrite X20', MEM'. psimpl. psimpl in NULL. exact NULL.
      clear - IHn READ2 NULL2. rename READ2 into READ. rename NULL2 into NULL.
      do 2 ISA_total_step.
      * eapply strcasecmp_advance. intros sadv hist XADV MADV RADV. apply IHn.
          unfold strcasecmp_readable, mem_readable in *. rewrite RADV. exact READ.
          rewrite XADV, MADV. psimpl. psimpl in NULL.
          rewrite N.add_1_l, N.add_succ_l, <- N.add_succ_r.
          exact NULL.
      * apply strcasecmp_finish. unfold strcasecmp_readable, mem_readable in *.
        psimpl. exact READ.
Qed.

(* A null byte outside the saved-register area survives every possible frame
   value.  Only this byte needs separation for termination; earlier input bytes
   may alias the frame, as in the original partial specification. *)
Lemma strcasecmp_null_survives:
  forall sp mem arg1 n fb
    (NULL: mem Ⓑ[arg1+n] = 0)
    (FRAME: 40 <= msub 64 (arg1+n) (sp ⊖ 48)),
  (setmem 64 LittleE 40 mem (sp ⊖ 48) fb) Ⓑ[arg1+n] = 0.
Proof.
  intros. rewrite getmem_1, setmem_frame by exact FRAME.
  rewrite <- (getmem_1 64 LittleE). exact NULL.
Qed.

Lemma strcasecmp_terminates:
  forall s sp mem arg1 n t
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X0: s R_X0 = arg1)
    (READ: strcasecmp_readable s) (WRITE: strcasecmp_writable s)
    (NULL: mem Ⓑ[arg1+n] = 0)
    (FRAME: 40 <= msub 64 (arg1+n) (sp ⊖ 48)),
  eventually strcasecmp strcasecmp_at_return ((Addr 1048576,s)::t).
Proof.
  intros. do 6 ISA_total_step.
  (* Earlier stores remain in the trace, so give each merged frame a
     fresh name instead of attempting to clear the preceding frame value. *)
  generalize_frame mem as fb0.
  try (generalize_frame mem as fb1).
  try (generalize_frame mem as fb2).
  try (generalize_frame mem as fb3).
  eapply strcasecmp_loop_terminates with (n:=n).
    unfold strcasecmp_readable, mem_readable in *. psimpl. exact READ.
    psimpl. apply strcasecmp_null_survives; assumption.
Qed.

(* This public theorem reuses the original invariant set and exit predicate.
   The extra assumptions are input data and memory permissions, not an
   operational success certificate. *)
Theorem strcmp_total_correctness:
  forall s sp mem arg1 arg2 a' n
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = a')
    (RX0: s R_X0 = arg1) (RX1: s R_X1 = arg2)
    (READ: strcasecmp_readable s) (WRITE: strcasecmp_writable s)
    (NULL: mem Ⓑ[arg1+n] = 0)
    (FRAME: 40 <= msub 64 (arg1+n) (sp ⊖ 48)),
  satisfies_total strcasecmp
    (invs1 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
    (exits1 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
    ((Addr 1048576,s)::nil).
Proof.
  intros. eapply total_of_partial with (entry:=(Addr 1048576,s)).
  - intros t' ORIGIN. destruct t' as [|[x' s'] hist].
      discriminate.
    rewrite ostartof_cons in ORIGIN. injection ORIGIN as ENTRY.
    eapply strcmp_partial_correctness; eassumption.
  - apply strcasecmp_first_exit.
    + eapply eventually_bind.
        eapply strcasecmp_terminates; eassumption.
      intros t' EX. apply EventuallyHere.
      destruct t' as [|[[a|i] s'] hist]; try contradiction.
      cbn [strcasecmp_at_return] in EX. subst a. reflexivity.
    + repeat split; try reflexivity; constructor; reflexivity.
Qed.

(* Expose a finite execution extension as well as demonic total correctness. *)
Corollary strcmp_finite_execution:
  forall s sp mem arg1 arg2 a' n
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = a')
    (RX0: s R_X0 = arg1) (RX1: s R_X1 = arg2)
    (READ: strcasecmp_readable s) (WRITE: strcasecmp_writable s)
    (NULL: mem Ⓑ[arg1+n] = 0)
    (FRAME: 40 <= msub 64 (arg1+n) (sp ⊖ 48)),
  exists prefix,
    exec_prog strcasecmp (prefix++(Addr 1048576,s)::nil) /\
    exit_post
      (invs1 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
      (exits1 sp mem a' arg1 arg2 (s R_X20) (s R_X21))
      (prefix++(Addr 1048576,s)::nil).
Proof.
  intros. eapply eventually_reaches.
    eapply strcmp_total_correctness; eassumption.
    constructor.
Qed.
