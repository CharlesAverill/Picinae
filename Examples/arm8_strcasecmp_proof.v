(* Example proof of correctness for an ARM8 implementation of strcasecmp,
   including subroutine tolower.  This demonstrates multi-subroutine
   code verification in Picinae.

   Credit: Proved by Kevin Hamlen while developing Picinae's multi-
     subroutine support logic, loosely based on an earlier attempt by
     students Nathaniel Simmons, Aaron Hill, Long Nguyen, Ariz Siddiqui.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
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
