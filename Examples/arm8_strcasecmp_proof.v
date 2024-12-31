(* Nathaniel Simmons, Aaron Hill, Long Nguyen, Ariz Siddiqui

   Code for CS 6335 Language-Based Security Class at UT Dallas

   To run this module, first load and compile:
   * Picinae_syntax
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_slogic
   * Picinae_armv8_pcode
   * strcasecmp_lo_strcasecmp_armv8
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Require Import Picinae_armv8_pcode.
Require Import arm8_strcasecmp.

Import ARM8Notations.
Open Scope N.

(* The ARMv8 lifter models non-writable code. *)
Theorem strcasecmp_nwc: 
	forall s2 s1, strcasecmp s1 = strcasecmp s2.
Proof. 
	reflexivity. 
Qed.

(* Example #1: Type safety *)
Theorem strcasecmp_welltyped: 
	welltyped_prog arm8typctx strcasecmp.
Proof.
  Picinae_typecheck.
Qed.

Theorem strcaselen_preserves_lr:
	forall_endstates strcasecmp (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strcasecmp_preserves_readable:
	forall_endstates strcasecmp (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strcasecmp_preserves_writable:
	forall_endstates strcasecmp (fun _ s _ s' => s A_WRITE = s' A_WRITE).
Proof.
	apply noassign_prog_same.
	prove_noassign.
Qed.

(* Define to_lower *)
Definition tolower (c:N) : N :=
  if andb (65 <=? c mod 2^32) (c mod 2^32 <=? 90) then (c mod 2^32 .| 32) else c.

(* Define binary-level string equality: *)
Definition strcaseeq (m: addr -> N) (p1 p2: addr) (k: N) :=
  ∀ i, i < k -> tolower (m Ⓑ[p1+i]) = tolower (m Ⓑ[p2+i]) /\ 0 < m Ⓑ[p1+i].

Section Invariants.

  Variable sp : N          (* initial stack pointer *).
  Variable mem : addr -> N (* initial memory state *).
  Variable raddr : N       (* R_X30 return address *).
  Variable arg1 : N        (* strcasecmp: R_X0 (1st pointer arg)
                              tolower: R_X0 input character *).
  Variable arg2 : N        (* strcasecmp: R_X1 (2nd pointer arg)
                              tolower: R_X19 (callee-save reg) *).
  Variable x20 x21 : value (* tolower: R_X20, R_X21 (callee-save regs) *).

  Definition mem' fbytes := setmem 64 LittleE 40 mem (sp ⊖ 48) fbytes.

  (* The post-condition says that interpreting EAX as a signed integer yields
     a number n whose sign equals the comparison of the kth byte in the two input
     strings, where the two strings are identical before k, and n may only be
     zero if the kth bytes are both nil. *)
  Definition postcondition (s:store) :=
    ∃ n k fb,
      s V_MEM64 = Ⓜ(mem' fb) /\
      s R_X0 = Ⓠn /\
      strcaseeq (mem' fb) arg1 arg2 k /\
      (n=0 -> (mem' fb) Ⓑ[arg1+k] = 0) /\ (* if the strings are equal, we're at the end of the strings *)
      (tolower (mem' fb Ⓑ[arg1+k]) ?= tolower(mem' fb Ⓑ[arg2+k])) = (toZ 32%N n ?= Z0)%Z.

  (* The invariant-set for this property makes minimal assumptions at program-start
     (address 1048576) except naming registers, and puts a loop-invariant at address 1048600. *)
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* Entry, x0 and x1 are the char strings *)
    | 1048576 => Inv 1 (
        s R_SP = Ⓠsp /\ s V_MEM64 = Ⓜmem /\
        s R_X0 = Ⓠarg1 /\ s R_X1 = Ⓠarg2
      )

    (* loop invariant *)
    | 1048600 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\
        s R_SP = Ⓠ(sp ⊖ 48) /\ s V_MEM64 = Ⓜ(mem' fb) /\
        s R_X19 = Ⓠ(arg2 ⊕ k) /\ s R_X20 = Ⓠ(arg1 ⊕ k)
      )

    (* Both letters must be either equal or case equal after toLower *)
    | 1048688 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\
        s R_SP = Ⓠ(sp ⊖ 48) /\ s V_MEM64 = Ⓜ(mem' fb) /\
        s R_X19 = Ⓠ(arg2 ⊕ k) /\ s R_X20 = Ⓠ(arg1 ⊕ k) /\
        (tolower(mem' fb Ⓑ[arg1 + k]) = tolower(mem' fb Ⓑ[arg2 + k])) /\
        mem' fb Ⓑ[arg1 + k] ≠ 0
      )

    (* One character is null or both are different after toLower *)
    | 1048648 => Inv 1 (∃ fb k,
        strcaseeq (mem' fb) arg1 arg2 k /\ (*characters before k matched*)
        s R_SP = Ⓠ(sp ⊖ 48) /\ s V_MEM64 = Ⓜ(mem' fb) /\
        s R_X19 = Ⓠ(arg2 ⊕ k) /\ s R_X20 = Ⓠ(arg1 ⊕ k) /\
          (tolower(mem' fb Ⓑ[arg1 + k]) ≠ tolower(mem' fb Ⓑ[arg2 + k]) \/
           mem' fb Ⓑ[arg1 + k] = 0)
      )

    (* Postcondition *)
    | 1048684 => Post 1 (postcondition s)

    (* tolower entry point *)
    | 2097152 => Inv 0 (s R_X0 = Ⓠarg1 /\ s R_X19 = Ⓠarg2 /\
         s R_X20 = x20 /\ s R_X21 = x21 /\
         s R_X30 = Ⓠraddr /\ s R_SP = Ⓠsp /\ s V_MEM64 = Ⓜmem)

    (* tolower return point *)
    | 2097168 => Post 0 (s R_X0 = Ⓠ(tolower arg1) /\ s R_X19 = Ⓠarg2 /\
         s R_X20 = x20 /\ s R_X21 = x21 /\
         s R_X30 = Ⓠraddr /\ s R_SP = Ⓠsp /\ s V_MEM64 = Ⓜmem)

    | _ => NoInv
    end.

  Definition exits0 := make_exits 0 strcasecmp invs.
  Definition invs0 := make_invs 0 strcasecmp invs.
  Definition exits1 := make_exits 1 strcasecmp invs.
  Definition invs1 := make_invs 1 strcasecmp invs.

End Invariants.

Lemma tolower_mod:
  forall c, (tolower c) mod 2^32 = tolower (c mod 2^32).
Proof.
  intro. unfold tolower. rewrite mp2_mod_mod. destruct (andb _ _).
    rewrite <- N.land_ones, N.land_lor_distr_l, N.land_ones, mp2_mod_mod. reflexivity.
    reflexivity.
Qed.

Lemma tolower_small:
  forall w e m a, tolower (getmem w e 1 m a) < 2^8.
Proof.
  intros. unfold tolower. destruct (andb _ _).
    apply lor_bound.
      rewrite <- getmem_mod_r, mp2_mod_mod_min. apply mp2_mod_lt.
      reflexivity.
    apply getmem_bound.
Qed.

Corollary tolower_byte:
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

Ltac step := time arm8_step.

Theorem tolower_correctness:
  forall s sp mem t xs' arg1 arg2 a'
         (ENTRY: startof t xs' = (Addr 2097152, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = Ⓠsp) (MEM: s V_MEM64 = Ⓜmem)
         (X0: s R_X0 = Ⓠarg1) (X19: s R_X19 = Ⓠarg2)
         (X30: s R_X30 = Ⓠa'),
  satisfies_all strcasecmp (invs0  sp mem a' arg1 arg2 (s R_X20) (s R_X21))
                           (exits0 sp mem a' arg1 arg2 (s R_X20) (s R_X21)) (xs'::t).
Proof.
  (* Start the proof the same way as before. *)
  intros. apply prove_invs.

  (* Prove the base case similarly. *)
  simpl. rewrite ENTRY. step. repeat split; assumption.

  (* Change assumptions about s into assumptions about s1. *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strcasecmp_welltyped).
  clear - PRE MDL. rename t1 into t.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 64 PRE.

  (* Address 152 (tolower entry point) *)
  destruct PRE as [X0 [X19 [X20 [X21 [X30 [SP MEM]]]]]].
  step. step. step.

    (* Address 164 *)
    step. repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). reflexivity. discriminate.

    (* Address 168 *)
    repeat split; try assumption.
    rewrite tolower_test in BC. unfold tolower.
    destruct (andb _ _). discriminate. reflexivity.
Qed.

(* Our partial correctness theorem makes the following assumptions:
   (ENTRY) Specify the start address and state of the subroutine.
   (MDL) Assume that on entry the processor is in a valid state.
   (ESP) Let esp be the value of the ESP register on entry.
   (MEM) Let mem be the memory state on entry.
   From these, we prove that all invariants (including the post-condition) hold
   true for arbitrarily long executions (i.e., arbitrary t). *)
Theorem strcmp_partial_correctness:
  forall s sp mem t s' x' arg1 arg2 a'
         (ENTRY: startof t (x',s') = (Addr 1048576, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = Ⓠsp) (MEM: s V_MEM64 = Ⓜmem) (X30: s R_X30 = Ⓠa')
         (RX0: s R_X0 = Ⓠarg1) (RX1: s R_X1 = Ⓠarg2),
  satisfies_all strcasecmp (invs1  sp mem a' arg1 arg2 (s R_X20) (s R_X21))
                           (exits1 sp mem a' arg1 arg2 (s R_X20) (s R_X21)) ((x',s')::t).
Proof.
  (* Start the proof the same way as before. *)
  intros. apply prove_invs.

  (* Prove the base case similarly. *)
  simpl. rewrite ENTRY. step. repeat split; assumption.

  (* Change assumptions about s into assumptions about s1. *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strcasecmp_welltyped).
  set (x20 := s R_X20) in *. set (x21 := s R_X21) in *. clearbody x20 x21.
  clear - PRE MDL. rename t1 into t. rename s1 into s.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 64 PRE.

  (* Address 1048576: Entry point *)
  destruct PRE as [MEM [SP [X0 X1]]].
  step. step. step. step. step. step.
  generalize_frame mem as fb.
  exists fb, 0. psimpl. split.
    intros i LT. destruct i; discriminate.
    repeat split.

  (* Address 1048600: Main loop *)
  destruct PRE as [fb [k [SEQ [SP [MEM [X19 X20]]]]]].
  step. step.

    (* Address 1048648: Reached null terminator in arg1 *)
    exists fb, k. repeat (reflexivity || assumption || split).
    right. apply N.eqb_eq, BC.

    (* Address 1048608: Character in arg1 is non-null. *)
    apply N.eqb_neq in BC.
    step. step.

      (* Address 1048648: Reached null terminator in arg2 *)
      apply N.eqb_eq in BC0.
      exists fb, k. repeat (reflexivity || assumption || split).
      left. rewrite BC0. change (tolower 0) with 0. unfold tolower.
      destruct (andb _ _).
        intro H. apply N.lor_eq_0_iff, proj2 in H. discriminate.
        assumption.

      (* Address 1048616: Current char in both strings are non-null. *)
      apply N.eqb_neq in BC0.
      step. step.

        (* Address 1048688: Equal characters found. *)
        eexists fb, k. repeat (assumption || reflexivity || split).
        apply N.eqb_eq in BC1. rewrite BC1. reflexivity.

        (* Address 1048624: Unequal characters found. Call tolower(arg1). *)
        step.
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
        set (x21' := s R_X21) in PRE. clearbody x21'.
        clear - SEQ BC BC0 BC1 PRE MDL'.
        rename MDL' into MDL. rename t' into t. rename a'0 into a. rename s' into s.

        destruct_inv 64 PRE.

        destruct PRE as [X0 [X19 [X20 [X21 [X30 [SP MEM]]]]]].
        clear X21 x21'.
        step. step. step. step.

        (* Another call to tolower *)
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

        destruct PRE as [X0 [X19 [X20 [X21 [X30 [SP MEM]]]]]].
        step. step. step.

          (* Address 1048688: Found equal characters. *)
          exists fb, k.
          rewrite !tolower_byte in BC2.
          repeat first [ assumption | split ].
          apply N.eqb_eq, BC2.

          (* Address 1048648: Found unequal characters. *)
          exists fb, k.
          rewrite !tolower_byte in BC2.
          repeat first [ assumption | split ].
          left. apply N.eqb_neq, BC2.

        (* Address 1048648: Loop back to loop invariant *)
        destruct PRE as [fb [k [SEQ [SP [MEM [X19 [X20 NEQ]]]]]]].
        step. step.

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

        destruct PRE as [X0 [X19 [X20 [X21 [X30 [SP MEM]]]]]].
        clear X21 x21'.
        step. step. step. step.

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

        destruct PRE as [X0 [X19 [X20 [X21 [X30 [SP MEM]]]]]].
        clear X21 x21'.
        step. step. step. step. step.
        eexists _, k, fb. repeat first [ reflexivity | assumption | split ].
          intro H. apply msub_move_0_r in H. destruct NEQ as [H'|H'].
            contradict H'. rewrite !tolower_byte in H. assumption.
            assumption.
          apply diff_compare; apply tolower_small.

  (* Address 1048688: Equal, non-nil chars (loop back) *)
  destruct PRE as [fb [k [SEQ [SP [MEM [X19 [X20 [EQ NN]]]]]]]].
  step. step. step.
  exists fb, (k+1). split.
    rewrite N.add_1_r. intros i H. apply N.lt_succ_r, N.le_lteq in H. destruct H.
      revert i H. apply SEQ.
      subst i. split. assumption. apply N.neq_0_lt_0, NN.
    psimpl. repeat split; assumption.
Qed.
