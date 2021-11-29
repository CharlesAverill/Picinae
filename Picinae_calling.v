(* Example proofs using Picinae for Intel x86 Architecture

   Copyright (c) 2021 Kevin W. Hamlen
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
Require Import List.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Picinae_i386.
Require Import Coq.Program.Equality.

Open Scope bool.
Open Scope list.
Open Scope N.

(* partial functions *)
Definition pfunc (A B:Type) := A -> option B.
Bind Scope pfunc_scope with pfunc.
Open Scope pfunc_scope.
Notation "x ⇀ y" := (pfunc x y) (at level 99, y at level 200, right associativity): type_scope.

(* the empty function (bottom) *)
Notation "⊥" := (fun _ => None).
Ltac einst0 H tac :=
  (lazymatch type of H with
   | ?t1 -> ?t2 =>
       let H0 := fresh in
       assert (H0: t1); [clear H|specialize (H H0); clear H0; einst0 H tac]
   | forall v, @?F v => epose proof (H ?[?v]) as H; einst0 H tac
   | _ => tac H
   end).

Ltac trivial2 := try solve [eassumption|discriminate|reflexivity].

Ltac einversion0 H has_intros has_trivial intros_patt :=
  let Htmp := fresh in
  pose proof H as Htmp; einst0 Htmp ltac:(fun H' =>
    lazymatch has_intros with
    | true => inversion H' as intros_patt; clear H'
    | false => inversion H'; clear H'
    end);
  lazymatch has_trivial with
  | true => trivial2
  | false => idtac
  end; subst.

Tactic Notation "einversion" constr(H) :=
  einversion0 H constr:(false) constr:(false) H.

Tactic Notation "einversion" "trivial" constr(H) :=
  einversion0 H constr:(false) constr:(true) H.

Tactic Notation "einversion" constr(H) "as" simple_intropattern(intros) :=
  einversion0 H constr:(true) constr:(false) intros.

Tactic Notation "einversion" "trivial" constr(H) "as" simple_intropattern(intros) :=
  einversion0 H constr:(true) constr:(true) intros.

Tactic Notation "einstantiate" constr(H) "as" simple_intropattern(Htmp) :=
  pose proof H as Htmp; einst0 Htmp ltac:(fun _ => idtac).

Tactic Notation "einstantiate" "trivial" constr(H) "as" simple_intropattern(Htmp):=
  einstantiate H as Htmp; trivial2.

Tactic Notation "einstantiate" constr(H) :=
  let Htmp := fresh in einstantiate H as Htmp.

Tactic Notation "einstantiate" "trivial" constr(H) :=
  let Htmp := fresh in einstantiate trivial H as Htmp.

Ltac invalid H := contradiction H; reflexivity.

Ltac contrapositive Equiv :=
  lazymatch goal with
  | [|- not _ <-> not _] =>
      let H := fresh in
      split; intro H; contradict H; eapply Equiv; try eassumption
  | _ => fail "Expects a contrapositive of the form ~ _ <-> ~ _"
  end.

(* Some equality definitions *)
Program Instance endian_EqDec: EqDec endianness.
Next Obligation. Proof. decide equality. Defined.

Program Instance binop_EqDec: EqDec binop_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance unop_EqDec: EqDec unop_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance cast_EqDec: EqDec cast_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance exp_EqDec: EqDec exp.
Next Obligation. Proof. decide equality; apply iseq. Defined.

Program Instance option_EqDec A `(EA : EqDec A) : EqDec (option A).
Next Obligation. Proof. decide equality. apply iseq. Defined.

(* Sets *)
Definition iseqb {A} {e: EqDec A} (a1 a2: A): bool :=
  if a1 == a2 then true else false.
Theorem iseqb_iff_eq: forall A (e: EqDec A) (a1 a2: A),
  iseqb a1 a2 = true <-> a1 = a2.
Proof.
  unfold iseqb. intros. destruct (a1 == a2).
  - subst. split; reflexivity.
  - split; try discriminate. intros. contradiction n.
Qed.

Theorem iseqb_iff_eq_contra: forall A (e: EqDec A) (a1 a2: A),
  iseqb a1 a2 = false <-> a1 <> a2.
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive iseqb_iff_eq.
Qed.

Inductive set (A: Type) :=
  | set_set (l: list A) (UNIQ: NoDup l).

Arguments set_set {_} _ _.

Definition set_nil {A} {e: EqDec A}: set A :=
  set_set nil (NoDup_nil A).
Definition set_elems {A} (s: set A): list A :=
  match s with set_set l _ => l end.
Theorem set_intros_l: forall {A} (s: set A) l UNIQ
  (EQ: s = set_set l UNIQ), l = set_elems s.
Proof. intros. subst. reflexivity. Qed.

Theorem set_elems_nodup: forall {A} (s: set A), NoDup (set_elems s).
Proof. intros. destruct s. assumption. Qed.

Definition set_has {A} {e: EqDec A} (s: set A) (a: A): bool :=
  existsb (iseqb a) (set_elems s).
Theorem existsb_iseqb_iff_in: forall A {e: EqDec A} l (a: A),
  existsb (iseqb a) l = true <-> In a l.
Proof.
  intros. split.
  - (* -> *) intro EXB. apply existsb_exists in EXB. destruct EXB as [a' [InL EQ]].
    apply iseqb_iff_eq in EQ. subst. assumption.
  - (* <- *) intro InL. apply existsb_exists. eexists. split. eassumption.
    apply iseqb_iff_eq. reflexivity.
Qed.

Theorem existsb_iseqb_iff_in_contra: forall A {e: EqDec A} l (a: A),
  existsb (iseqb a) l = false <-> ~(In a l).
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive existsb_iseqb_iff_in.
Qed.

Theorem set_has_in: forall {A} {e: EqDec A} a s,
  set_has s a = true <-> In a (set_elems s).
Proof.
  unfold set_has, set_elems. split; subst; intro; eapply existsb_iseqb_iff_in;
  assumption.
Qed.
Corollary set_has_in_contra: forall {A} {e: EqDec A} (s: set A) a,
  set_has s a = false <-> ~In a (set_elems s).
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive set_has_in.
Qed.

Fixpoint set_compact' {A} {e: EqDec A} (l: list A): list A :=
  match l with
  | nil => nil
  | h :: t =>
      let l' := set_compact' t in
      if existsb (iseqb h) l'
      then l' else h :: l'
  end.
Theorem set_compact_nodup: forall {A} {e: EqDec A} (l: list A), NoDup (set_compact' l).
Proof.
  induction l.
  - constructor.
  - simpl. destruct existsb eqn: EXB. assumption.
    apply existsb_iseqb_iff_in_contra in EXB. constructor; assumption.
Qed.
Definition set_compact {A} {e: EqDec A} (s: set A): set A :=
  let l := set_elems s in
  set_set (set_compact' l) (set_compact_nodup l).

Definition set_add' {A} {e: EqDec A} (s: set A) (a: A): list A :=
  if (set_has s a) then set_elems s else a :: set_elems s.
Theorem set_add_nodup {A} {e: EqDec A} (s: set A) (a: A): NoDup (set_add' s a).
Proof.
  destruct s. unfold set_add'.
  destruct set_has eqn: EX.
  - (* Already exists, so we just return l *) assumption.
  - (* Does not exists, we can return (a :: l) *) econstructor; [|eassumption].
    intro InL. eapply set_has_in_contra in EX. apply EX. assumption.
Qed.
Definition set_add {A} {e: EqDec A} (s: set A) (a: A): set A :=
  if (set_has s a) then s else set_set (set_add' s a) (set_add_nodup s a).
(*
Theorem fold_set_add: forall A (e: EqDec A) s (a: A),
  set_add' s a = set_elems (set_add s a).
Proof. intros. reflexivity. Qed.
 *)

Theorem set_rewrite: forall A (l1 l2: list A) (UNIQ1: NoDup l1) (EQ: l1 = l2),
  exists UNIQ2, set_set l1 UNIQ1 = set_set l2 UNIQ2.
Proof. intros. subst. exists UNIQ1. reflexivity. Qed.

(*Axiom nodup_unique: forall A (l: list A) (U1 U2: NoDup l), U1 = U2.*)

Theorem set_add_idempotent: forall A (e: EqDec A) (s: set A) a
  (InOld: In a (set_elems s)), set_add s a = s.
Proof.
  intros. assert (set_add' s a = set_elems s).
    unfold set_add'. destruct set_has eqn: SH; try reflexivity.
    apply set_has_in in InOld. rewrite InOld in SH. discriminate.
  unfold set_add. destruct set_has eqn: SH; try reflexivity.
  apply set_has_in_contra in SH. contradiction SH.
Qed.

Theorem set_add_preserves: forall A (e: EqDec A) (s: set A) a1 a2
  (InOld: In a1 (set_elems s)), In a1 (set_elems (set_add s a2)).
Proof.
  intros. unfold set_add. destruct set_has eqn: SH.
  - assumption.
  - simpl. unfold set_add'. rewrite SH. right. assumption.
Qed.
Theorem set_add_frame: forall A (e: EqDec A) (s: set A) a1 a2
  (NEQ: a1 ≠ a2) (InAdd: In a1 (set_elems (set_add s a2))), In a1 (set_elems s).
Proof.
  intros. simpl in *. unfold set_add in *. destruct set_has eqn: SH.
  - assumption.
  - simpl in InAdd. unfold set_add' in *. rewrite SH in InAdd.
    destruct InAdd; [|assumption]. subst. contradiction NEQ. reflexivity.
Qed.
Theorem set_add_correct: forall A (e: EqDec A) (s: set A) a,
  In a (set_elems (set_add s a)).
Proof.
  unfold set_add, set_elems. intros.
  destruct s. destruct set_has eqn: EX.
  - (* contains a *) apply set_has_in in EX. assumption.
  - (* no contains a *) unfold set_add'. rewrite EX. left. reflexivity.
Qed.

Fixpoint set_ap' {A} {e: EqDec A} (l1: list A) (s2: set A): set A :=
  match l1 with
  | nil => s2
  | h::t => set_add (set_ap' t s2) h
  end.
Definition set_ap {A} {e: EqDec A} (s1 s2: set A): set A :=
  set_ap' (set_elems s1) s2.
Theorem fold_set_ap: forall {A} {e: EqDec A} {l1} (UNIQ1: NoDup l1) (s2: set A),
  set_ap' l1 s2 = set_ap (set_set l1 UNIQ1) s2.
Proof. reflexivity. Qed.

Theorem set_ap_correct: forall A (e: EqDec A) (s1 s2: set A) a,
  (In a (set_elems s1) \/ In a (set_elems s2)) <->
  In a (set_elems (set_ap s1 s2)).
Proof.
  unfold set_ap. destruct s1 as [l1 UNIQ1], s2 as [l2 UNIQ2]. split.
  - (* -> *) intro In12. destruct In12 as [In1|In2]; simpl in *; clear UNIQ1.
    + (* In1 *) revert In1. induction l1; intros.
      * (* nil *) inversion In1.
      * (* no nil *) inversion In1.
        -- (* a = a0 *) subst. simpl. apply set_add_correct.
        -- (* a in l *) simpl. apply set_add_preserves. apply IHl1; assumption.
    + (* In2 *) induction l1.
      * (* nil *) assumption.
      * (* no nil *) simpl. apply set_add_preserves. apply IHl1.
  - (* <- *) intro InRes. simpl in *. clear UNIQ1. revert l2 UNIQ2 a InRes.
    induction l1; intros.
    + (* nil *) right. assumption.
    + (* no nil *) simpl in InRes. destruct (a0 == a); subst.
      * (* a = a0 *) left. left. reflexivity.
      * (* a ≠ a0 *) apply set_add_frame in InRes; [|assumption].
        einversion trivial IHl1 as [InL1|InL2].
        -- left. right. assumption.
        -- right. assumption.
Qed.
Corollary set_ap_left: forall A (e: EqDec A) (s1 s2: set A) a
  (In1: In a (set_elems s1)), In a (set_elems (set_ap s1 s2)).
Proof. intros. apply set_ap_correct. left. assumption. Qed.
Corollary set_ap_right: forall A (e: EqDec A) (s1 s2: set A) a
  (In2: In a (set_elems s2)), In a (set_elems (set_ap s1 s2)).
Proof. intros. apply set_ap_correct. right. assumption. Qed.
Corollary set_ap_incl_l: forall A (e: EqDec A) (s1 s2: set A),
  incl (set_elems s1) (set_elems (set_ap s1 s2)).
Proof. unfold incl. intros. apply set_ap_left; assumption. Qed.
Corollary set_ap_incl_r: forall A (e: EqDec A) (s1 s2: set A),
  incl (set_elems s2) (set_elems (set_ap s1 s2)).
Proof. unfold incl. intros. apply set_ap_right; assumption. Qed.
Theorem set_ap_has_split: forall A (e: EqDec A) (s1 s2: set A) a,
  set_has (set_ap s1 s2) a = set_has s1 a || set_has s2 a.
Proof.
  intros. destruct set_has eqn: SHres.
  - apply set_has_in in SHres. apply set_ap_correct in SHres.
    repeat rewrite <- set_has_in in SHres. apply orb_true_intro in SHres.
    symmetry. assumption.
  - apply set_has_in_contra in SHres. symmetry. apply orb_false_intro;
    destruct set_has eqn: SH; try reflexivity; apply set_has_in in SH;
    contradict SHres; apply set_ap_correct; (left + right); assumption.
Qed.
Corollary set_ap_has_l: forall A (e: EqDec A) (s1 s2: set A) a
  (SH1: set_has s1 a = true), set_has (set_ap s1 s2) a = true.
Proof.
  intros. rewrite set_ap_has_split. rewrite SH1. apply orb_true_l.
Qed.
Corollary set_ap_has_r: forall A (e: EqDec A) (s1 s2: set A) a
  (SH2: set_has s2 a = true), set_has (set_ap s1 s2) a = true.
Proof.
  intros. rewrite set_ap_has_split. rewrite SH2. apply orb_true_r.
Qed.
Corollary set_ap_has_contra_l: forall A (e: EqDec A) (s1 s2: set A) a
  (SHres: set_has (set_ap s1 s2) a = false), set_has s1 a = false.
Proof.
  intros. rewrite set_ap_has_split in SHres. apply orb_false_elim in SHres.
  destruct SHres. assumption.
Qed.
Corollary set_ap_has_contra_r: forall A (e: EqDec A) (s1 s2: set A) a
  (SHres: set_has (set_ap s1 s2) a = false), set_has s2 a = false.
Proof.
  intros. rewrite set_ap_has_split in SHres. apply orb_false_elim in SHres.
  destruct SHres. assumption.
Qed.

Theorem set_ap_incl_equal: forall A (e: EqDec A) s1 s2
  (Incl: incl (set_elems s1) (set_elems s2)),
  set_elems (set_ap s1 s2) = set_elems s2.
Proof.
  intros until s1. destruct s1 as [l1 UNIQ1]. simpl. induction l1; intros.
  - reflexivity.
  - unfold set_ap. simpl. apply incl_cons_inv in Incl. destruct Incl.
    inversion UNIQ1. subst. rewrite set_add_idempotent. eapply IHl1; assumption.
    erewrite fold_set_ap. apply set_ap_right. assumption.
Unshelve. all: assumption.
Qed.

Definition set_length {A} (s: set A): nat := length (set_elems s).

Definition set_equivb {A} {e: EqDec A} (s1 s2: set A): bool :=
  ((set_length s1 =? set_length s2) &&
  (set_length s1 =? set_length (set_ap s1 s2)))%nat.

Definition set_equiv {A} (s1 s2: set A): Prop :=
  incl (set_elems s1) (set_elems s2) /\ incl (set_elems s2) (set_elems s1).

Notation "a ~=~ b" := (set_equiv a b) (at level 80, right associativity): type_scope.

Theorem set_equiv_refl: forall A (s1 s2: set A),
  s1 ~=~ s1 -> s1 ~=~ s1.
Proof. intros. split; apply incl_refl. Qed.

Theorem set_equiv_symm: forall A (s1 s2: set A),
  s1 ~=~ s2 -> s2 ~=~ s1.
Proof. intros. destruct H. split; assumption. Qed.

Theorem set_equiv_tran: forall A (s1 s2 s3: set A),
  s1 ~=~ s2 -> s2 ~=~ s3 -> s1 ~=~ s3.
Proof. intros. destruct H, H0. split; eapply incl_tran; eassumption. Qed.

Theorem set_equiv_intro: forall {A} (s1 s2: set A),
  incl (set_elems s1) (set_elems s2) ->
  incl (set_elems s2) (set_elems s1) -> s1 ~=~ s2.
Proof. intros. split; assumption. Qed.

Theorem set_add_equiv_equal: forall A (e: EqDec A) s s' a
  (SAP: set_add s a = s') (Equiv: s ~=~ s'), s = s'.
Proof.
  unfold set_add, set_equiv. intros. destruct s. destruct s'.
  inversion SAP. clear SAP. destruct Equiv. destruct l; simpl in *.
  - (* nil *) destruct l0; try discriminate. einversion (H1 a0). left. reflexivity.
  - (* non-nil *) destruct l0. einversion (H a0). left. reflexivity.
    destruct set_has eqn: SH.
    + (* a is in l *) simpl in H0. inversion H0. subst. reflexivity.
    + (* a is not in l *) inversion H0. subst. clear H0. unfold set_add' in H3.
      simpl in H3. rewrite SH in H3. inversion H3. subst. einstantiate (H1 a1).
      left. reflexivity.
      (* Either we have duplication or contradict our SH *)
      destruct (a1 == a0).
      * subst. inversion UNIQ0. subst. contradiction H5.
      * inversion H0. symmetry in H2. contradiction n.
        apply set_has_in_contra in SH. contradict SH. assumption.
Qed.

Theorem set_ap_equiv_equal: forall A (e: EqDec A) s1 s2 s2'
  (SAP: set_ap s1 s2 = s2') (Equiv: s2' ~=~ s2),
  s2 = s2'.
Proof.
  unfold set_ap. intros until s1. destruct s1 as [l1 UNIQ1]. simpl.
  induction l1; intros.
  - simpl in SAP. subst. reflexivity.
  - inversion UNIQ1. subst. simpl in *.
    (* Show that equivalence across an add implies equivalence in the
       underlying AP *)
    assert (EQ_AP: s2 ~=~ set_ap' l1 s2). {
      destruct Equiv as [NoAdd _].
      erewrite (fold_set_ap H2). split; intros a2 HIn.
      - apply set_ap_right. assumption.
      - apply NoAdd, set_add_preserves. erewrite (fold_set_ap H2).
        assumption.
    }
    einstantiate trivial set_add_equiv_equal as EQ_ADD. apply set_equiv_symm.
    eapply set_equiv_tran; eassumption. rewrite <- EQ_ADD.
    apply set_equiv_symm in EQ_AP. apply IHl1; solve [assumption|reflexivity].
Qed.

Theorem set_equiv_has: forall A (e: EqDec A) (s1 s2: set A) a
  (Equiv: s1 ~=~ s2), set_has s1 a = set_has s2 a.
Proof.
  intros. destruct set_has eqn: SH1.
  - apply set_has_in in SH1. symmetry. apply set_has_in. apply Equiv.
    assumption.
  - apply set_has_in_contra in SH1. symmetry. apply set_has_in_contra.
    intro. apply SH1. apply Equiv. assumption.
Qed.

(* Show that by checking if the sets are equal size that they must be
 * equivalent *)
Theorem set_equivb_iff_equiv: forall A (e: EqDec A) (s1 s2: set A),
  set_equivb s1 s2 = true <-> s1 ~=~ s2.
Proof.
  intros. unfold set_equiv, set_equivb, set_length. destruct s1 as [l1 UNIQ1],
    s2 as [l2 UNIQ2], set_ap as [l_res UNIQ_res] eqn: SAP.
  assert (Incl_1_res: incl l1 l_res). intros a In1.
    erewrite set_intros_l by eassumption. apply set_ap_left. assumption.
  assert (Incl_2_res: incl l2 l_res). intros a In2.
    erewrite set_intros_l by eassumption. apply set_ap_right. assumption.

  split.
  - (* -> *) intro LEQ. apply andb_prop in LEQ. destruct LEQ as [L12 L1U].
    apply Nat.eqb_eq in L12, L1U. simpl in L12, L1U.
    assert (Incl_res_1: incl l_res l1).
      eapply NoDup_length_incl; try eassumption. rewrite L1U. reflexivity.
    assert (Incl_res_2: incl l_res l2).
      eapply NoDup_length_incl; try eassumption. rewrite <- L12, L1U. reflexivity.
    split; eapply incl_tran; eassumption.
  - (* <- *) intros [Incl_12 Incl_21].
    (* Show that l_res ≡ l1 by showing that it must be containing either l1 or l2
     * and that l1 ≡ l2. *)
    assert (Incl_res_1: incl l_res l1). intros a InRes.
      remember (set_set _ _) as s1. remember (set_set l2 _) as s2.
      remember (set_set l_res _) as s_res.
      einversion trivial (set_ap_correct _ _ s1 s2) as [_ [In1|In2]].
      erewrite set_intros_l in InRes. eassumption. eassumption.
      assumption. apply Incl_21. assumption.

    (* Given the sets are all equivalent, we show they are the same size too. *)
    simpl. einstantiate trivial (@NoDup_incl_length _ l1 l_res).
    einstantiate trivial (@NoDup_incl_length _ l_res l1).
    erewrite (Nat.le_antisymm (length l_res)) by eassumption.
    einstantiate trivial (@NoDup_incl_length _ l1 l2) as Le1.
    einstantiate trivial (@NoDup_incl_length _ l2 l1) as Le2.
    erewrite (Nat.le_antisymm (length l1)) by eassumption.
    rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem set_equivb_if_equiv: forall A (e: EqDec A) (s1 s2: set A),
  s1 ~=~ s2 -> set_equivb s1 s2 = true.
Proof. apply set_equivb_iff_equiv. Qed.

Theorem set_equality_equiv: forall A {e: EqDec A} (s1 s2: set A)
  (EQ: set_elems s1 = set_elems s2), s1 ~=~ s2.
Proof.
  intros. einstantiate set_equivb_iff_equiv. apply H. destruct s2.
  unfold set_equivb, set_length, set_ap. rewrite EQ, (fold_set_ap UNIQ),
  set_ap_incl_equal, Nat.eqb_refl by apply incl_refl. reflexivity.
Qed.

(* We define a store delta as a variable to partial mapping onto
 * some expression. This is partial to account for "undefined" variables (which
 * could also be undefined "memory" variables) *)
Definition store_delta := var -> option exp.

Definition has_delta (h: hdomain) (s0 s: store) (δ: store_delta) :=
  forall v e val (LUv: δ v = Some e) (EE: eval_exp h s0 e val), s v = val.

(*
Definition safety (c0: typctx) (se: simple_exp) :=
  forall v0 off w (EQ_V: se = VarOff v0 off w), c0 v0 = Some (NumT w).

Definition delta_safety (c0: typctx) (δ: store_delta) :=
  forall v, safety c0 (δ v).

Definition delta_models (c0 c: typctx) (δ: store_delta) :=
  forall v t (CV: c v = Some t) (NotCpx: δ v <> Complex), hastyp_simple_exp c0 (δ v) t.
*)

Definition delta_nounk (δ: store_delta) :=
  forall v e (LUv: δ v = Some e), forall_exps_in_exp not_unknown e.

Definition delta_differentb vars (δ1 δ2: store_delta) :=
  existsb (fun v => if δ1 v == δ2 v then false else true) vars.

Definition delta_different (δ1 δ2: store_delta) :=
  exists v, δ1 v <> δ2 v.

Definition delta_same (δ1 δ2: store_delta) :=
  forall v, δ1 v = δ2 v.

Definition delta_same_domain (δ1 δ2: store_delta) :=
  forall v, match (δ1 v), (δ2 v) with
            | Some _, Some _ => True
            | None, None => True
            | _, _ => False
            end.

Definition domain_total vars (δ: store_delta) :=
  forall v e, δ v = Some e -> In v vars.

Theorem delta_different_differentb_equiv: forall vars δ1 δ2
  (DT1: domain_total vars δ1) (DT2: domain_total vars δ2),
  delta_differentb vars δ1 δ2 = true <-> delta_different δ1 δ2.
Proof.
  unfold delta_different, delta_differentb, domain_total. split.
  - (* -> *) intro DDB. unfold delta_different. apply existsb_exists in DDB.
    destruct DDB as [v [InDomain EQ]]. eexists. destruct iseq. discriminate.
    eassumption.
  - (* <- *) intro DB. apply existsb_exists. destruct DB as [v NEQ]. eexists.
    split; [|vantisym (δ1 v) (δ2 v); [reflexivity|assumption]].
    destruct (δ1 v) eqn: LU1; destruct (δ2 v) eqn: LU2;
      (* When one is not empty *) try ((eapply DT1 + eapply DT2); eassumption).
      (* Both are empty, discriminate. *) rewrite <- LU1 in NEQ.
      contradiction (NEQ eq_refl).
Qed.

Corollary delta_different_differentb_equiv_contra: forall vars δ1 δ2
  (DT1: domain_total vars δ1) (DT2: domain_total vars δ2),
  delta_differentb vars δ1 δ2 = false <-> ~ delta_different δ1 δ2.
Proof.
  intros. einstantiate trivial (delta_different_differentb_equiv vars δ1 δ2) as Equiv.
  split.
  - intros N_DDB DB. apply Equiv in DB. rewrite N_DDB in DB. discriminate.
  - intros N_DD. destruct delta_differentb; try reflexivity.
    contradiction N_DD. apply Equiv. reflexivity.
Qed.

Theorem delta_different_same: forall δ1 δ2,
  delta_same δ1 δ2 <-> ~ delta_different δ1 δ2.
Proof.
  split.
  - (* -> *) intro DS. intro. destruct H. apply H. apply DS.
  - (* <- *) intros DS. intro v. destruct (δ1 v == δ2 v); try assumption.
    destruct DS. exists v. apply n.
Qed.

Lemma models_assign: forall c h s v e u t (MDL: models c s)
  (TE: hastyp_exp c e t) (EE: eval_exp h s e u),
  models (c [v := Some t]) (s [v := u]).
Proof.
  unfold models. intros. destruct (v0 == v).
  - subst. rewrite update_updated. rewrite update_updated in CV. inversion CV.
    subst. eapply preservation_eval_exp; eassumption.
  - rewrite update_frame by assumption. rewrite update_frame in CV by
    assumption. apply MDL in CV. assumption.
Qed.

Lemma neq_sym: forall A (n m: A), n <> m -> m <> n.
Proof.
  intros. intro. subst. apply H. reflexivity.
Qed.

Lemma has_delta_assign_None: forall h s s' δ v u (HD: has_delta h s s' δ),
  has_delta h s (s' [v := u]) (δ [v := None]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite update_frame in LUv by assumption.
    rewrite update_frame in * by assumption. eapply HD; eassumption.
Qed.

Lemma has_delta_assign_Some: forall h s s' δ v e u (HD: has_delta h s s' δ)
  (EQ: forall u' (EE: eval_exp h s e u'), u = u'),
  has_delta h s (s' [v := u]) (δ [v := Some e]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite update_updated in LUv.
    inversion LUv; subst. apply EQ. assumption.
  - apply neq_sym in n. rewrite update_frame in LUv by assumption.
    rewrite update_frame in * by assumption. eapply HD; eassumption.
Qed.

Lemma delta_nounk_assign_None: forall v δ (DNU: delta_nounk δ),
  delta_nounk (δ [v := None]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Lemma delta_nounk_assign_Some: forall v δ e (DNU: delta_nounk δ)
  (NUnk: forall_exps_in_exp not_unknown e),
  delta_nounk (δ [v := Some e]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite update_updated in LUv. inversion LUv; subst. assumption.
  - apply neq_sym in n. rewrite update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Theorem delta_same_domain_refl: forall δ, delta_same_domain δ δ.
Proof.
  unfold delta_same_domain. intros.
  destruct (δ v); reflexivity.
Qed.

Theorem delta_same_domain_assign: forall v δ1 δ2 o1 o2
  (Sim: match o1, o2 with
        | Some _, Some _ => True
        | None, None => True
        | _, _ => False
        end)
  (DSD: delta_same_domain δ1 δ2),
  delta_same_domain (δ1 [v := o1]) (δ2 [v := o2]).
Proof.
  unfold delta_same_domain. intros. destruct (v == v0).
  - subst. repeat rewrite update_updated. destruct o1, o2;
    solve [reflexivity|contradiction Sim].
  - apply neq_sym in n. repeat rewrite update_frame by assumption. apply DSD.
Qed.

Fixpoint subst_valid (δ: store_delta) e: bool :=
  match e with
  | Var v =>
      match δ v with
      | Some e => true
      | None => false
      end
  | Word _ _ => true
  | Load e1 e2 _ _ => subst_valid δ e1 && subst_valid δ e2
  | Store e1 e2 e3 _ _ => subst_valid δ e1 && subst_valid δ e2 && subst_valid δ e3
  | BinOp _ e1 e2 => subst_valid δ e1 && subst_valid δ e2
  | UnOp _ e => subst_valid δ e
  | Cast _ _ e => subst_valid δ e
  | Let v e e_in =>
      if subst_valid δ e
      then subst_valid (update δ v (Some (Word 0 0))) e_in
      else subst_valid (update δ v None) e_in
  | Unknown _ => false
  | Ite e1 e2 e3 => subst_valid δ e1 && subst_valid δ e2 && subst_valid δ e3
  | Extract _ _ e => subst_valid δ e
  | Concat e1 e2 => subst_valid δ e1 && subst_valid δ e2
  end.

Fixpoint subst_exp0 (δ: store_delta) e: exp :=
  match e with
  | Var v =>
      match δ v with
      | Some e => e
      | None => Unknown 0 (* Note we should return error in subst_err here *)
      end
  | Word _ _ => e
  | Load e1 e2 en len => Load (subst_exp0 δ e1) (subst_exp0 δ e2) en len
  | Store e1 e2 e3 en len => Store (subst_exp0 δ e1) (subst_exp0 δ e2)
      (subst_exp0 δ e3) en len
  | BinOp op e1 e2 => BinOp op (subst_exp0 δ e1) (subst_exp0 δ e2)
  | UnOp op e => UnOp op (subst_exp0 δ e)
  | Cast typ w' e => Cast typ w' (subst_exp0 δ e)
  | Let v e e_in =>
      if subst_valid δ e
      then subst_exp0 (update δ v (Some (subst_exp0 δ e))) e_in
      else subst_exp0 (update δ v None) e_in
  | Unknown _ => e
  | Ite e1 e2 e3 => Ite (subst_exp0 δ e1) (subst_exp0 δ e2) (subst_exp0 δ e3)
  | Extract n1 n2 e => Extract n1 n2 (subst_exp0 δ e)
  | Concat e1 e2 => Concat (subst_exp0 δ e1) (subst_exp0 δ e2)
  end.

Definition subst_exp (δ: store_delta) e: option exp :=
  if subst_valid δ e then Some (subst_exp0 δ e) else None.

Theorem subst_valid_any_Some: forall e δ1 δ2
  (DSD: delta_same_domain δ1 δ2),
  subst_valid δ1 e = subst_valid δ2 e.
Proof.
  induction e; intros; simpl; try erewrite IHe1 by eassumption;
  try erewrite IHe2 by eassumption; try erewrite IHe3 by eassumption;
  try erewrite IHe by eassumption; try reflexivity.

  (* Var *) specialize (DSD v). destruct (δ1 v), (δ2 v);
  try solve [contradiction DSD|reflexivity].

  (* Let *) destruct subst_valid eqn: SV1; erewrite IHe2; try reflexivity;
  (apply delta_same_domain_assign; [reflexivity|assumption]).
Qed.

Local Ltac exp_destruction_nounk :=
  lazymatch goal with
  | δ: store_delta |- _ =>
      (* Specialize the δ, allowing destruct to do automatic rewrites *)
      repeat match goal with
             | IH: forall (δ0: store_delta), _ |- _ => specialize (IH δ)
             end;
      (* Destruct on all the subst_valid _ e? *)
      repeat destruct (subst_valid _ _); inversion SE;
      (* Destruct on any conditionals *)
      repeat match goal with
             | n: N |- _ => destruct n
             end;
      repeat lazymatch goal with
             | IH: forall (DNU: delta_nounk δ), _ |- _ =>
                 einstantiate trivial IH as IH
             end
  end.

Theorem subst_exp0_nounk: forall e δ (DNU: delta_nounk δ)
  (SE: subst_valid δ e = true), forall_exps_in_exp not_unknown (subst_exp0 δ e).
Proof.
  unfold subst_exp; induction e; intros; simpl in SE;
  try solve [exp_destruction_nounk; repeat split; assumption + reflexivity].
  - (* Var *) destruct (δ v) eqn: LUv; inversion SE. subst. eapply DNU. simpl.
    rewrite LUv. reflexivity.
  - (* Let *) simpl. destruct subst_valid eqn: SV1.
    + (* e1 is valid *) apply IHe2. apply delta_nounk_assign_Some. assumption.
      apply IHe1; assumption. erewrite subst_valid_any_Some. eassumption.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) apply IHe2. apply delta_nounk_assign_None.
      assumption. assumption.
Qed.

Theorem subst_exp_nounk: forall e e' δ (DNU: delta_nounk δ)
  (SE: subst_exp δ e = Some e'), forall_exps_in_exp not_unknown e'.
Proof.
  unfold subst_exp. intros. destruct subst_valid eqn: SV; inversion SE.
  subst. apply subst_exp0_nounk; assumption.
Qed.

Ltac exp_destruction_correct :=
  lazymatch goal with
  | δ: store_delta, e': exp |- _ =>
      lazymatch goal with
      | SE: _ = Some e', EE': eval_exp _ _ e' _ |- _ =>
          (* Specialize the δ, allowing destruct to do automatic rewrites *)
          repeat match goal with
                 | IH: forall (δ0: store_delta), _ |- _ => specialize (IH δ)
                 end;
          (* Destruct on all the subst_valid _ e? *)
          repeat destruct (subst_valid _ _);
          (* Do rest of inversions *)
          inversion SE; subst; inversion EE'; subst;
          (* Destruct on any conditionals *)
          repeat match goal with
                 | n: N |- _ => destruct n
                 end;
          repeat lazymatch goal with
                 | IH: forall (e': exp), _ |- _ =>
                     einstantiate trivial IH as IH; inversion IH
                 end
      end
  end.

Theorem subst_exp_correct: forall s0 h e e' s δ v v'
  (HD: has_delta h s0 s δ) (SE: subst_exp δ e = Some e') (EE: eval_exp h s e v)
  (EE': eval_exp h s0 e' v'), v = v'.
Proof.

  intros. move δ before e. repeat lazymatch goal with H:_ |- _ => revert H end.

  unfold subst_exp; induction e; intros; inversion EE; subst;
  simpl in SE; clear EE; try solve [exp_destruction_correct; reflexivity].
  - (* Var *) destruct (δ v) eqn: LUv; inversion SE. subst. erewrite HD;
    solve [reflexivity|eassumption].
  - (* Let *) destruct subst_valid eqn: SV1.
    + (* e1 is valid *) erewrite subst_valid_any_Some in SE. eapply IHe2;
      [| eassumption | eassumption | eassumption]. apply has_delta_assign_Some.
      assumption. intros. destruct (subst_valid _ e2) eqn: SV2; inversion SE.
      eapply IHe1; try eassumption. rewrite SV1. reflexivity.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) eapply IHe2; [| eassumption | eassumption | eassumption].
      apply has_delta_assign_None. assumption.
  - (* Ite *) exp_destruction_correct. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe2 as IHe2.
Qed.

(*
Lemma delta_safety_assign: forall c0 v se δ (DS: delta_safety c0 δ)
  (SSE: safety c0 se), delta_safety c0 (δ [v := se]).
Proof.
  unfold delta_safety, safety. intros.
  destruct (v == v0).
  - (* accessing our newly scoped variable *) subst.
    rewrite update_updated in EQ_V. eapply SSE. eassumption.
  - (* accessing some other variable *) apply neq_sym in n.
    rewrite update_frame in EQ_V by assumption. eapply DS. eassumption.
Qed.

Lemma delta_models_weaken: forall c0 c c' δ (DMDL: delta_models c0 c δ)
  (SS: c' ⊆ c), delta_models c0 c' δ.
Proof.
  unfold delta_models. intros.
  apply DMDL; try apply SS; assumption.
Qed.

Lemma delta_models_assign: forall c0 c v δ se t (DMDL: delta_models c0 c δ)
  (TSE: se = Complex \/ hastyp_simple_exp c0 se t),
  delta_models c0 (c [v := Some t]) (δ [v := se]).
Proof.
  unfold delta_models. intros.
  destruct (v == v0).
  - subst. rewrite update_updated in *. rewrite update_updated in CV.
    inversion CV. subst. destruct TSE; [contradiction NotCpx|].
    inversion H; constructor; try assumption.
  - apply neq_sym in n. rewrite update_frame in CV by assumption.
    rewrite update_frame in * by assumption. destruct (δ _) eqn: LUv0;
    try invalid NotCpx; rewrite <- LUv0 in *; einversion trivial DMDL;
    rewrite LUv0; rewrite LUv0 in H1; inversion H1; subst; constructor;
    assumption.
Qed.
 *)

Definition trace_states := (addr ⇀ store_delta).

  (*
 * list addr)%type.
Definition trace_states_prop := (trace_states * (var -> option Prop))%type.
   *)
Definition trace_state_res := option (list (store_delta * option exit)).
Definition trace_state_res_with_prop :=
  option (list (store_delta * option exit) * (var -> option Prop)).

Fixpoint map_option {A B} (f: A -> option B) (l: list A): option (list B) :=
  match l with
  | nil => Some nil
  | a :: t =>
      match f a with
      | None => None
      | Some b =>
          match map_option f t with
          | None => None
          | Some t' => Some (b :: t')
          end
      end
  end.

Theorem map_option_inductive_principal: forall {A B} (P: list A -> list B -> Prop)
  al bl (f: A -> option B) (MAPS: map_option f al = Some bl) (BASE: P nil nil)
  (INDUCT: forall a b (F: f a = Some b) al bl (MO: map_option f al = Some bl)
    (IHab: P al bl), P (a :: al) (b :: bl)),
  P al bl.
Proof.
  induction al; intros.
  - inversion MAPS. exact BASE.
  - inversion MAPS. destruct (f a) eqn: F; inversion H0. clear H0.
    destruct (map_option _ al) eqn: MO; try inversion H1. subst. clear H1.
    apply INDUCT; try assumption. eapply IHal; try solve [eassumption|reflexivity].
Qed.

Tactic Notation "induction_map" ident(al) "maps_to" ident(bl) :=
  (first [ revert dependent al; intro al; revert dependent bl; intros bl
         | intros until al; intros until bl] ||
  fail "No quantified hypothesis for" al "or" bl);
  repeat lazymatch goal with
         | [H: ?HType |- _] =>
             lazymatch HType with
             | map_option ?f al = Some bl => fail
             | _ => intro
             end
         end;
  let typ := uconstr:(map_option ?f al = Some bl) in
  pattern al, bl; eapply map_option_inductive_principal;
  [intros; (eassumption||fail "No quantified hypothesis to satisfy " typ)
  | | intro; intro; intro; intro; intro; intro; intro ].

Lemma map_option_includes: forall A B (f: A -> option B) l l'
  (Maps: map_option f l = Some l') a b (F: f a = Some b) (InL: In a l),
  In b l'.
Proof.
  induction l.
    intros. simpl in Maps. inversion InL.
    intros. simpl in Maps. destruct f eqn:DF; try solve [inversion Maps].
      destruct (map_option); inversion Maps.
      inversion InL.
        subst. rewrite DF in F. inversion F. subst. constructor. reflexivity.
        destruct l'; try solve [inversion H0]. apply in_cons. clear DF Maps InL H0 a. eapply IHl.
          reflexivity. apply F. assumption.
Qed.

Lemma map_option_fails: forall A B (f: A -> option B) l a
  (F: f a = None) (InL: In a l), map_option f l = None.
Proof.
  induction l; intros.
  - inversion InL.
  - inversion InL; subst.
    + simpl. rewrite F. reflexivity.
    + simpl. erewrite IHl; try eassumption. destruct (f a); reflexivity.
Qed.

Fixpoint simple_trace_stmt (δ: store_delta) (q: stmt): trace_state_res :=
  match q with
  | Nop => Some ((δ, None) :: nil)
  | Move v e => Some ((δ[v := subst_exp δ e], None) :: nil)
  | Jmp e =>
      match subst_exp δ e with
      | Some (Word n _) => Some ((δ, Some (Exit n)) :: nil)
      | _ => None
      end
  | Exn n => Some ((δ, Some (Raise n)) :: nil)
  | Seq q1 q2 =>
      match simple_trace_stmt δ q1 with
      | None => None
      | Some paths1 =>
          let res := map_option (fun '(δ', x) =>
            match x with
            | None =>
                match simple_trace_stmt δ' q2 with
                | None => None
                | Some paths2 => Some paths2
                end
            | Some _ => Some ((δ', x) :: nil)
            end) paths1 in
          match res with
          | None => None
          | Some ll => Some (concat ll)
          end
      end
  | If _ q1 q2 =>
      match simple_trace_stmt δ q1, simple_trace_stmt δ q2 with
      | None, _ | _, None => None
      | Some paths1, Some paths2 =>
          Some (paths1 ++ paths2)
      end
  | Rep _ s => None
  end.

(*
Theorem preservation_simple_trace_stmt: forall c0 s0 q paths c c' δ
  (MDL0: models c0 s0) (STyp: hastyp_stmt c0 c q c')
  (DMDL: delta_models c0 c δ) (DS: delta_safety c0 δ)
  (STS: simple_trace_stmt δ q = Some paths),
  Forall (fun '(δ', x') => x' = None -> delta_models c0 c' δ') paths.
Proof.
  induction q; intros; inversion STyp; inversion STS; subst; clear STyp STS;
  repeat constructor; intros.
  - (* Nop *) eapply delta_models_weaken; eassumption.
  - (* Move *) unfold delta_models. intros. destruct (v0 == v); subst.
    + (* v0 = v *) rewrite update_updated. rewrite update_updated in NotCpx.
      einversion trivial (eval_simple_exp_total s0). apply safety_simplify_exp.
      assumption. einstantiate trivial (SS v). rewrite update_updated in H0.
      inversion H0. subst. clear H0. eapply preservation_simplify_exp; eassumption.
    + (* v0 <> v *) rewrite update_frame by assumption.
      rewrite update_frame in NotCpx by assumption. apply DMDL.
      erewrite <- (update_frame c) by eassumption. apply SS. assumption.
      assumption.
  - (* Jump *) destruct simplify_exp eqn: SE; inversion H2. subst.
    repeat constructor. discriminate.
  - (* Exception *) discriminate.
  - (* Seq *) destruct simple_trace_stmt eqn: STS1; try discriminate.
    destruct map_option eqn: MO; inversion H3. subst. rename l into paths1.
    rename l0 into paths_res. clear H3. einstantiate trivial IHq1 as DMp1.
    einstantiate trivial safety_simple_trace_stmt as DSp1.
    clear STS1 IHq1. revert DMp1. induction_map paths1 maps_to paths_res; intros.
    constructor. apply Forall_app. clear paths1 paths_res MO.
    rename b into paths_res, al into paths1, bl into paths'. split.
    + (* Top case *) destruct a as [δ1 [x1|]]; inversion F; subst; clear F.
      -- repeat constructor. discriminate.
      -- destruct (simple_trace_stmt _ q2) eqn: STS2; inversion H0. subst. clear H0.
         inversion DMp1. inversion DSp1. subst. specialize (H1 eq_refl).
         eapply IHq2; try eassumption. eapply hastyp_stmt_weaken; try eassumption.
    + (* Inductive case *) inversion DSp1. inversion DMp1. subst.
      eapply IHab; eassumption.
  - (* If *) destruct simple_trace_stmt eqn: STS1; try discriminate.
    destruct (simple_trace_stmt _ q2) eqn: STS2; try discriminate. inversion H4.
    subst. apply Forall_app. eapply hastyp_stmt_weaken in TS1; try eassumption.
    eapply hastyp_stmt_weaken in TS2; try eassumption. split;
      (eapply IHq1 + eapply IHq2); eassumption.
Qed.
*)

Theorem simple_trace_stmt_correct: forall s0 q paths h s s' x δ
  (HD: has_delta h s0 s δ) (XS: exec_stmt h s q s' x)
  (STS: simple_trace_stmt δ q = Some paths),
  Exists (fun '(δ', x') => x' = x /\ has_delta h s0 s' δ') paths.
Proof.
  induction q; intros; inversion XS; inversion STS; subst; clear XS STS.
  - (* Nop *) constructor. split. reflexivity. assumption.
  - (* Move *) constructor. split. reflexivity. destruct subst_exp eqn: SE1.
    + apply has_delta_assign_Some. assumption. intros.
      eapply subst_exp_correct; eassumption.
    + apply has_delta_assign_None. assumption.
  - (* Jmp *) destruct (subst_exp _ _) eqn: SE; try destruct e0; inversion H3.
    subst. constructor. split; try assumption.
    einstantiate trivial subst_exp_correct as Res. constructor. inversion Res.
    reflexivity.
  - (* Exn *) constructor. split. reflexivity. assumption.
  - (* Seq, exit 1 *) destruct simple_trace_stmt as [paths1|] eqn: SQ1; try discriminate.
    einstantiate trivial (IHq1). destruct map_option eqn: Map; inversion H4.
    subst. clear H4. rename l into paths_res. apply Exists_exists in H.
    destruct H as [[δ1 x1] [InP1 [X HD1]]]; subst. apply Exists_exists.
    exists (δ1, Some x0). repeat split; [|assumption]. apply in_concat. eexists.
    split; [|apply in_eq]. eapply map_option_includes; try eassumption.
    reflexivity.
  - (* Seq, exit 2 *) destruct (simple_trace_stmt) eqn:SQ1; [|discriminate].
    destruct map_option eqn:MO; inversion H4. subst. clear H4. einstantiate
    trivial IHq1. apply Exists_exists in H. apply Exists_exists.
    destruct H as [[δ1 x1] [InP1 [X HD1]]]. subst.
    destruct (simple_trace_stmt δ1 q2) eqn:SQ2.
    + einstantiate IHq2 as IHq2; try assumption; try apply SQ2; try apply TS2;
      try apply XS0; try eassumption. apply Exists_exists in IHq2.
      destruct IHq2 as [[δ' x'] [Inl1 HD']]. eexists. split.

      (* Prove that state is in concat l0 *) apply in_concat. eexists.
      split; try eassumption. eapply map_option_includes; try eassumption.
      simpl. rewrite SQ2. reflexivity. simpl. assumption.
    + erewrite map_option_fails in MO; try solve [discriminate|eassumption].
      simpl. rewrite SQ2. reflexivity.
  - (* If/else *) destruct c;
    (destruct (simple_trace_stmt) eqn: ST1; [|discriminate]);
    (destruct (simple_trace_stmt δ q2) eqn: ST2; [|discriminate]).
    + (* q2 *) einstantiate trivial IHq2. eapply incl_Exists.
      inversion H5. apply incl_appr. apply incl_refl. assumption.
    + (* q1 *) einstantiate trivial IHq1. eapply incl_Exists.
      inversion H5. apply incl_appl. apply incl_refl. assumption.
Qed.

Definition join_states_if_changed (vars: list var) (δ1: option store_delta)
  (δ2: store_delta): option store_delta :=
  match δ1 with
  | Some δ1 =>
      if delta_differentb vars δ1 δ2
      then Some (fun v => if δ1 v == δ2 v then δ2 v else None)
      else None
  | None => Some δ2
  end.

Definition null_state: store := fun _ => VaN 0 0.

Definition h_conj h1 h2 := fun (v: var) =>
  match h1 v, h2 v with
  | None, p | p, None => p
  | Some p1, Some p2 => Some (p1 /\ p2)
  end.

Definition true_hyp {V} hyps (v:V) :=
  match hyps v with
  | Some hyp => hyp
  | None => True
  end.

Definition process_state (vars: list var) (exitof: option exit -> exit)
  (st: store_delta * option exit) (accum: trace_states * bool) :=
  let '(ts, changed) := accum in
  let '(δ', x) := st in
  (* If this exited to an address, update state on that address
   * Otherwise if it is a raise, we don't actually care about
   * what state we end up in (nothing to merge with), since
   * there is no way for us to return back later on to a valid
   * address. *)
  match exitof x with
  | Exit next_addr =>
      (* Check if joining states changed something. If so, we update and mark
       * this as changed *)
      match join_states_if_changed vars (ts next_addr) δ' with
      | Some δ_merge => (update ts next_addr (Some δ_merge), true)
      | None => (ts, changed)
      end
  | Raise _ => (ts, changed)
  end.

Definition sub_prog p domain: program :=
  fun s a => if existsb (iseqb a) domain then p s a else None.

Theorem exec_sub_prog_pmono: forall d1 d2 p s h a n s' x
  (SS: incl d1 d2) (XP: exec_prog h (sub_prog p d1) a s n s' x),
  exec_prog h (sub_prog p d2) a s n s' x.
Proof.
  intros. apply (exec_prog_pmono (sub_prog p d1)); [|assumption].
  unfold sub_prog, pfsub. intros s0 x0 [sz q] ImpD1.
  destruct existsb eqn: E1; destruct (existsb _ d2) eqn: E2;
  try solve [discriminate|assumption]. rewrite existsb_iseqb_iff_in in E1.
  rewrite existsb_iseqb_iff_in_contra in E2. contradict E2.
  apply SS. assumption.
Qed.

Definition stmt_correct q δ x := forall s0 h s s' (XS: exec_stmt h s q s' x),
  has_delta h s0 s' δ.

Definition correctness_sub_prog p domain ts h a0 s0 :=
  (forall a1 s1 n1 δ
    (XP: exec_prog h (sub_prog p domain) a0 s0 n1 s1 (Exit a1))
    (TS2: ts a1 = Some δ), has_delta h s0 s1 δ).

Inductive subgoals: Set :=
  .

Definition trace_program_step_at (vars: list var) (p: program)
  (hints: program -> addr -> trace_states -> option (trace_states * bool))
  addr (accum: option (trace_states * bool)) :=
  match accum with
  | None => None
  | Some (ts, changed) =>
      (* Use hints if we have information *)
      match hints p addr ts with
      | None =>
          (* If this is a proper address in program, process that. *)
          match p null_state addr with
          (* TODO: some logic saying that for all possible executions that there
           * exists some point later on in this execution such that it matches
           * one of the store deltas that we recorded. *)
          | None => None (*Some (ts, working, P)*)
          | Some (sz, q) =>
              (* Sanity check for if we have already visited this address *)
              match ts addr with
              | None => None
              | Some δ_a =>
                  match simple_trace_stmt δ_a q with
                  | None => None
                  | Some next_states =>
                      let res := fold_right (process_state vars
                        (exitof (addr + sz))) (ts, changed) next_states in
                      Some res
                  end
              end
          end
      | Some (ts', changed') => Some (ts', changed || changed')
      end
  end.

Definition expand_trace_program (vars: list var) (p: program)
  (hints: program -> addr -> trace_states -> option (trace_states * bool))
  (reachable: set addr) (init_ts: trace_states): option (trace_states * bool) :=
  fold_right (trace_program_step_at vars p hints) (Some (init_ts, false))
    (set_elems reachable).

Lemma fold_expand_trace_program: forall vars p hints reachable init_ts,
  fold_right (trace_program_step_at vars p hints) (Some (init_ts, false))
    (set_elems reachable) =
  expand_trace_program vars p hints reachable init_ts.
Proof. reflexivity. Qed.

Inductive exec_prog2 (h: hdomain) (p:program) (a:addr) (s:store): nat -> store -> exit -> Prop :=
| X2Done: exec_prog2 h p a s O s (Exit a)
| X2Step n sz q s2 a1 s' x' (LU: p s2 a1 = Some (sz,q))
        (XP: exec_prog2 h p a s n s2 (Exit a1))
        (XS: exec_stmt h s2 q s' x'):
    exec_prog2 h p a s (S n) s' (exitof (a1+sz) x')
| X2Abort sz q s' i (LU: p s a = Some (sz,q))
         (XS: exec_stmt h s q s' (Some (Raise i))):
    exec_prog2 h p a s (S O) s' (Raise i).

Theorem exec_prog_equiv_exec_prog2: forall n h p a s s' x,
  (exec_prog h p a s n s' x <-> exec_prog2 h p a s n s' x).
Proof.
  induction n; intros.
  - (* n = 0 *) split; intros XP; inversion XP; subst; constructor.
  - split; intros XP.
    + (* -> *) inversion XP; try econstructor; try eassumption; subst.
      destruct n.
      * (* n = 1 *) inversion XP0. subst. rewrite <- EX. econstructor;
        try eassumption. constructor.
      * rewrite <- Nat.add_1_r in XP0. einstantiate trivial exec_prog_split as XPS.
        destruct XPS as [s1 [a1 [XP_middle XP_end]]]. inversion XP_end. subst.
        inversion XP1. subst. rewrite <- EX0. econstructor; try eassumption.
        apply IHn. rewrite <- Nat.add_1_l. eapply exec_prog_concat;
        [|apply XP_middle]. econstructor; try eassumption. econstructor.
        subst. replace (Raise i) with (exitof (a1+sz0) (Some (Raise i))).
        econstructor; try eassumption. apply IHn. rewrite <- Nat.add_1_l.
        eapply exec_prog_concat; try eassumption. econstructor; try eassumption.
        econstructor. reflexivity.
    + (* <- *) inversion XP; try solve [econstructor; eassumption]. subst.
      destruct n.
      * (* n = 1 *) inversion XP0. subst. destruct exitof eqn: EX.
        -- econstructor; try eassumption. constructor.
        -- destruct x'; try discriminate. eapply XAbort. eassumption.
           destruct e; inversion EX. subst. assumption.
      * apply IHn in XP0. rewrite <- Nat.add_1_r. eapply exec_prog_concat;
        try eassumption. destruct exitof eqn: EX.
        -- econstructor; try eassumption. constructor.
        -- destruct x'; try discriminate. eapply XAbort. eassumption.
           destruct e; inversion EX. subst. assumption.
Qed.

Theorem trace_program_step_at_steady_correct: forall p vars a_new al hints ts
  h a0 s0 (Init: forall δ s, ts a0 = Some δ -> has_delta h s s δ)
  (IHal: correctness_sub_prog p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
  (Total: Forall (fun a1 => exists δ1, ts a1 = Some δ1) (a_new :: al))
  (TPSA: trace_program_step_at vars p hints a_new (Some (ts, false)) =
    Some (ts, false))
  (HintsCorrect: forall a_new al ts h a0 s0
    (IHal: correctness_sub_prog p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
    (Total: Forall (fun a1 => exists δ1, ts a1 = Some δ1) (a_new :: al))
    (Hint: hints p a_new ts = Some (ts, false)),
    correctness_sub_prog p (a_new :: al) ts h a0 s0),
  correctness_sub_prog p (a_new :: al) ts h a0 s0.
Proof.
  (* Destruct trace_program_step_at function. *)
  unfold correctness_sub_prog. intros. simpl in TPSA.

  (* Using hint if available *)
  destruct hints as [[ts' changed']|] eqn: Hint. inversion TPSA. subst.
  eapply HintsCorrect; try eassumption. clear HintsCorrect.

  destruct (p _ _) as [[sz_new q_new]|] eqn: LUa_new; try discriminate.
  destruct (ts a_new) as [δ_a_new|] eqn: TSa_new; try discriminate.
  destruct simple_trace_stmt as [next_states|] eqn: Fn; try discriminate.
  rename a1 into a', s1 into s', n1 into n', δ into δ', XP into XP',
    TS2 into TS'.

  (* Main case has the flow a0 ~> a1 -> a' *)
  apply exec_prog_equiv_exec_prog2 in XP'. revert a' s' δ' XP' TS'.
  induction n'; intros; inversion XP'; subst.
  - (* n = 0 *) apply Init. assumption.
  - (* n > 0 *) rename s2 into s1. eapply Forall_forall in Total.
    destruct Total as [δ1 TS1]. einstantiate trivial IHn' as HD1.

    (* Here we need to prove that process_state correctly processes all states,
     * i.e. given that the deltas are correct up to a1, we show that the deltas
     * are correct for a'. We know that a1 flows into a'. We should check if
     * a' == a_new. If it is, we check correctness of that, otherwise we use
     * inductive hypothesis *)
    admit.
    (*destruct (a' == a_new). subst. admit.*)

    (* Prove that a1 is in the domain. Holds true because a1 was in the
     * sub-program because of our execution flow, so must be in subdomain. *)
    unfold sub_prog in LU. destruct existsb eqn: EXa2; try discriminate.
    apply existsb_exists in EXa2. destruct EXa2 as [a1' [InDomain Eq]].
    destruct (a1 == a1'); try discriminate. subst. assumption.
Admitted.
Definition hintCorrect hints p : Prop := forall a_new al ts h a0 s0
    (IHal: correctness_sub_prog p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
    (Total: Forall (fun a1 => exists δ1, ts a1 = Some δ1) (a_new :: al))
    (Hint: hints p a_new ts = Some (ts, false)),
    correctness_sub_prog p (a_new :: al) ts h a0 s0.

(*MARK*)
(*
Theorem expand_trace_program_steady_correct: forall p vars hints reachable ts
  h a0 s0 
  (INIT: forall δ, ts a0 = Some δ -> has_delta h s0 s0 δ)
  (HINT: hintCorrect hints p)
  (TPO: expand_trace_program vars p hints reachable ts = Some (ts, false)),
  correctness_sub_prog p (set_elems reachable) ts h a0 s0.
Proof.
  intros. revert HINT INIT. revert TPO s0. revert a0 h ts hints vars p. destruct reachable as [reachable_addrs UNIQ_reachable_addrs]. 
  induction reachable_addrs.
  - intros. unfold correctness_sub_prog. intros. simpl in XP. inversion XP. subst. apply INIT. assumption. inversion LU. 
  - intros. unfold correctness_sub_prog in *. simpl in *.
      unfold expand_trace_program in TPO. unfold expand_trace_program. simpl in *.
      unfold trace_program_step_at in TPO. destruct fold_right in TPO; try solve [inversion TPO].
      destruct p0 in TPO. destruct (hints) in TPO. 
      + simpl in TPO. destruct p0 in TPO. inversion TPO.

  - intros. unfold correctness_sub_prog in IHreachable_addrs. intros. 
      simpl in IHreachable_addrs. eapply IHreachable_addrs.
      unfold expand_trace_program in TPO. unfold expand_trace_program. simpl in TPO. simpl.
      unfold trace_program_step_at in TPO. destruct fold_right in TPO; try solve [inversion TPO].
      destruct p0 in TPO. destruct (hints) in TPO. 
      + simpl in TPO. destruct p0 in TPO. inversion TPO.
Qed.
 *)
Theorem test: forall (p : store → addr → option (N * stmt)) hints reachable ts p vars q sz s2 a2
    (TPO : expand_trace_program vars p hints reachable ts = Some (ts, false))
    (LU : sub_prog p (set_elems reachable) s2 a2 = Some (sz, q)),
    exists δ, ts a2 = Some δ.
Proof.
  intros. revert TPO LU. revert ts vars q sz s2 a2. destruct reachable as [reachable_addrs UNIQ_reachable_addrs]. 
  (*intros.  unfold expand_trace_program in TPO. unfold trace_program_step_at in TPO.*)
  induction reachable_addrs.
  - intros. subst. simpl in TPO. unfold sub_prog in LU. simpl in LU. inversion LU.
  - intros. 
    simpl in LU. unfold sub_prog in LU. destruct existsb; try discriminate.
    unfold expand_trace_program in *. simpl in *. unfold trace_program_step_at in TPO.
    destruct fold_right eqn:H_fr; try solve [inversion TPO].    
    destruct p1 eqn:H_p1. destruct hints in TPO. admit. simpl in TPO. 
    destruct p0 eqn:H_p; try solve [inversion TPO]. destruct p1; try solve [inversion TPO]. 
    destruct t; try solve [inversion TPO]. destruct simple_trace_stmt; try solve [inversion TPO]. inversion TPO.
    unfold expand_trace_program.

    eapply IHreachable_addrs. clear IHreachable_addrs.
    intros. 
Theorem expand_trace_program_steady_correct_n: forall p vars hints reachable ts
  h a0 s0 
  (INIT: forall δ, ts a0 = Some δ -> has_delta h s0 s0 δ)
  (HINT: hintCorrect hints p)
  (TPO: expand_trace_program vars p hints reachable ts = Some (ts, false)),
  correctness_sub_prog p (set_elems reachable) ts h a0 s0.
Proof.
  unfold correctness_sub_prog. intros. revert HINT INIT XP TS2 TPO. revert a0 h ts hints vars p s0 a1 s1 δ. induction n1.
  - intros.  simpl in XP. inversion XP. subst. apply INIT. assumption.
  - intros. apply exec_prog_equiv_exec_prog2 in XP. inversion XP. subst. einstantiate IHn1.
      exact HINT.
      exact INIT.
      apply exec_prog_equiv_exec_prog2 in XP0. exact XP0.   
      2: { exact TPO. } 
      unfold expand_trace_program in TPO. simpl in TPO. unfold trace_program_step_at in TPO.



Qed.






















Theorem expand_trace_program_steady_correct: forall p vars hints reachable ts
  h a0 s0 (Init: forall δ s, ts a0 = Some δ -> has_delta h s s δ)
  (TPO: expand_trace_program vars p hints reachable ts = Some (ts, false))
  (HintsCorrect: forall a_new al ts h a0 s0
    (IHal: correctness_sub_prog p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
    (Total: Forall (fun a1 => exists δ1, ts a1 = Some δ1) (a_new :: al))
    (Hint: hints p a_new ts = Some (ts, false)),
    correctness_sub_prog p (a_new :: al) ts h a0 s0),
  correctness_sub_prog p (set_elems reachable) ts h a0 s0.
Proof.
  intros until reachable. destruct reachable as [al UNIQ_al]. revert UNIQ_al.
  induction al; intros; unfold correctness_sub_prog; intros.
  - unfold sub_prog in XP. simpl in XP. inversion XP; subst.
    + apply Init. assumption.
    + inversion LU.
  - inversion UNIQ_al as [|? ? InAl UNIQ_al']. subst.
    unfold expand_trace_program in TPO. simpl in TPO.
    erewrite (set_intros_l _ al UNIQ_al') in TPO by reflexivity.
    rewrite fold_expand_trace_program in TPO.
    eapply trace_program_step_at_steady_correct; try eassumption.
    eapply IHal; try eassumption. admit. (* trivial *)
    admit. (* trivial *)
    admit. (* trivial *)
Admitted.

Fixpoint stmt_reachable (s: stmt): option (set addr * bool) :=
  match s with
  | Nop => Some (set_nil, true)
  | Move _ _ => Some (set_nil, true)
  | Jmp e =>
      match e with
      | Word loc _ => Some (set_add set_nil loc, false)
      | _ => None
      end
  | Exn _ => Some (set_nil, false)
  | Seq s1 s2 =>
      match (stmt_reachable s1, stmt_reachable s2) with
      | (Some (j1, false), _) => Some (j1, false)
      | (_, None) => None
      | (None, _) => None
      | (Some (j1, true), Some (j2, falls2)) => Some (set_ap j1 j2, falls2)
      end
  | If _ s1 s2 =>
      match (stmt_reachable s1, stmt_reachable s2) with
      | (_, None) => None
      | (None, _) => None
      | (Some (j1, falls1), Some (j2, falls2)) =>
          Some (set_ap j1 j2, falls1 || falls2)
      end
  | Rep _ s =>
      match stmt_reachable s with
      | Some (jmps, falls) => Some (jmps, true)
      | None => None
      end
  end.

Definition reachables_at (hints: addr -> option (set addr))
  (p: program) (a: addr) (accum: option (set addr)) :=
  match accum with
  | Some jmps =>
      match hints a with
      | Some jmps' => Some (set_ap jmps' jmps)
      | None =>
          match p null_state a with
          | Some (sz, q) =>
              match stmt_reachable q with
              | Some (sjmps, falls) => Some
                  (set_ap (if falls
                  then set_add sjmps (a+sz)
                  else sjmps) jmps)
              | None => None
              end
          | None => None
          end
      end
  | None => None
  end.

Definition iterM (n: N) {A} (f: A -> option A) (x: A) :=
  N.iter n (fun x => match x with Some x => f x | None => None end) (Some x).

Definition expand_reachables (hints: addr -> option (set addr))
  (p: program) (reachable: set addr) :=
  match fold_right (reachables_at hints p) (Some reachable)
    (set_elems reachable) with
  | Some reachable' =>
      Some (if set_equivb reachable reachable'
      then (reachable, false)
      else (reachable', true))
  | None => None
  end.

Definition expand_reachables_fast (hints: addr -> option (set addr))
  (p: program) (accum: list addr * list addr): option (list addr * list addr) :=
  let '(reachable, frontier) := accum in
  match fold_right (reachables_at hints p) (Some set_nil)
    frontier with
  | Some reachable' =>
      Some (fold_right (fun a '(reachable, frontier) =>
        if existsb (iseqb a) reachable
        then (reachable, frontier)
        else (a :: reachable, a :: frontier)) (reachable, nil)
      (set_elems reachable'))
  | None => None
  end.

Definition expand_reachables_n (hints: addr -> option (set addr))
  (p: program) (reachable: set addr) (n: N) :=
  iterM n (fun x: (set addr * bool) => let '(x, b) := x in
    if b then expand_reachables hints p x else Some (x, false)) (reachable, true).

Definition expand_reachables_fast_n (hints: addr -> option (set addr))
  (p: program) (accum: list addr * list addr) (n: N): option (list addr * list addr) :=
  iterM n (expand_reachables_fast hints p) accum.

Lemma rep_exits_total: forall e q h s s' x a
  (XS: exec_stmt h s (Rep e q) s' x) (EX: x = Some a),
  exists s0 s0', exec_stmt h s0 q s0' x.
Proof.
  intros. inversion XS; subst; clear XS; simpl in *.
  rewrite N2Nat.inj_iter in XS0. remember (N.to_nat n) as nn.
  clear e w E n Heqnn. revert q h s s' a XS0.
  induction nn; intros. inversion XS0. inversion XS0; subst; clear XS0.
  - eexists. eexists. eassumption.
  - eapply IHnn. eassumption.
Qed.

Theorem stmt_reachable_complete: forall q h s0 s1 x jmps falls
  (XS: exec_stmt h s0 q s1 x)
  (JMPS: stmt_reachable q = Some (jmps, falls)),
  match x with
  | Some (Exit a') => set_has jmps a' = true
  | Some (Raise _) => True
  | None => falls = true
  end.
Proof.
  induction q; intros; inversion XS; subst; simpl in *.
  - (* Nop *) inversion JMPS. reflexivity.
  - (* Assign *) inversion JMPS. reflexivity.
  - (* Jmp *) inversion E; subst; simpl in *; clear E; try discriminate.
    inversion JMPS. eapply set_has_in. apply set_add_correct.
  - (* Exn *) reflexivity.
  - (* Seq, exit in q1 *) destruct (stmt_reachable q1) as [[j1 falls1]|] eqn: J1;
    try solve [destruct (stmt_reachable q2) eqn: J2; discriminate]. destruct falls1.
    + (* Can fall-through *) destruct x0; try reflexivity.
      destruct (stmt_reachable q2) as [[j2 falls2]|] eqn: J2; try discriminate.
      inversion JMPS. subst. apply set_ap_has_l. einstantiate trivial IHq1.
    + (* Cannot fall-through *) inversion JMPS. subst. destruct x0;
      try reflexivity. einstantiate trivial IHq1.
  - (* Seq, exit in q2 *) destruct (stmt_reachable q1) as [[j1 falls1]|] eqn: J1;
    try solve [destruct (stmt_reachable q2) eqn: J2; discriminate]. destruct falls1.
    + (* Can fall-through *) destruct (stmt_reachable q2) as [[j2 falls2]|] eqn: J2;
      try discriminate. inversion JMPS. subst. einstantiate trivial IHq2 as IHq2.
      destruct x as [[a|n]|]; trivial2. apply set_ap_has_r. assumption.
    + (* Cannot fall-through; contradiction *) inversion JMPS.
      subst. einstantiate trivial IHq1 as IHq1.
  - (* If *) destruct (stmt_reachable q1) as [[j1 falls1]|] eqn: J1;
    destruct (stmt_reachable q2) as [[j2 falls2]|] eqn: J2; try discriminate.
    inversion JMPS. subst. clear JMPS. destruct x as [[a|n]|]; try reflexivity.
    + (* Jumped *) rewrite set_ap_has_split. apply orb_true_intro.
      destruct c; [einstantiate trivial IHq2; right|
        einstantiate trivial IHq1; left]; eassumption.
    + (* Fallthrough *) apply orb_true_intro. destruct c;
      [einstantiate trivial IHq2; right | einstantiate trivial IHq1; left];
      assumption.
  - (* Evil rep *) destruct stmt_reachable as [[jmps' falls']|] eqn: Jinner;
    inversion JMPS. subst. destruct x as [[a|?]|]; try reflexivity.
    einstantiate trivial rep_exits_total as RET.
    destruct RET as [s2 [s2' XSinner]]. einstantiate trivial IHq.
Qed.

Lemma reachables_incl: forall hints p a reaches' mreaches
  (RA: reachables_at hints p a mreaches = Some reaches'),
  exists reaches0, mreaches = Some reaches0 /\
    incl (set_elems reaches0) (set_elems reaches').
Proof.
  unfold reachables_at. intros. destruct mreaches; try discriminate.
  eexists. repeat split. destruct hints eqn: Hints.
  - inversion RA. subst. intros a2 InS. apply set_ap_right. assumption.
  - destruct p as [[sz q]|] eqn: LU; try discriminate.
    destruct stmt_reachable as [[jmps falls]|] eqn: SRQ; try discriminate.
    inversion RA. subst. intros a2 InS. apply set_ap_right. assumption.
Qed.

Lemma reachables_equiv_equal: forall hints p a reaches reaches'
  (RA: reachables_at hints p a (Some reaches) = Some reaches')
  (EQ: reaches ~=~ reaches'), reaches = reaches'.
Proof.
  intros. unfold reachables_at in RA.
  destruct EQ. destruct hints.
  - inversion RA. subst. eapply set_ap_equiv_equal. reflexivity.
    split; assumption.
  - destruct p as [[sz q]|]; try discriminate.
    destruct stmt_reachable as [[sjmps falls]|]; inversion RA.
    subst. eapply set_ap_equiv_equal. reflexivity.
    split; assumption.
Qed.

Lemma fold_right_reachables_incl: forall hints p addrs reaches reaches'
  (RA: fold_right (reachables_at hints p) (Some reaches) addrs = Some reaches'),
  incl (set_elems reaches) (set_elems reaches').
Proof.
  unfold incl. induction addrs; intros.
  - inversion RA. subst. assumption.
  - simpl in RA. einversion trivial reachables_incl as [reaches1 [EQ Incl]].
    apply Incl. eapply IHaddrs; eassumption.
Qed.

Lemma destruct_reachables_at_prin: forall {P hints p a_new reaches reaches'}
  (RA: reachables_at hints p a_new (Some reaches) = Some reaches')
  (PHints: forall hints_res
    (Hints: hints a_new = Some hints_res)
    (RA': set_ap hints_res reaches = reaches'), P a_new)
  (PDefault: forall sz q sjmps falls
    (LU: p null_state a_new = Some (sz, q))
    (SR: stmt_reachable q = Some (sjmps, falls))
    (RA': set_ap (if falls then set_add sjmps (a_new + sz) else sjmps)
      reaches = reaches'),
    P a_new),
  P a_new.
Proof.
  intros. simpl in RA.
  destruct hints eqn: Hints. inversion RA. subst. eapply PHints; reflexivity.
  destruct p as [[sz q]|] eqn: LU; try discriminate.
  destruct stmt_reachable as [[sjmps falls]|] eqn: SR; inversion RA. subst.
  eapply PDefault; solve [reflexivity|eassumption].
Qed.

Ltac destruct_reachables_at RA :=
  lazymatch type of RA with
  | reachables_at _ _ ?a_new (Some _) = Some _ =>
      move RA before a_new; revert dependent a_new;
      intros a_new RA; pattern a_new; apply (destruct_reachables_at_prin RA);
      intros; clear RA; subst
  end.

Lemma fold_right_reachables_equiv_equal: forall hints p addrs reaches reaches'
  (RA: fold_right (reachables_at hints p) (Some reaches) addrs = Some reaches')
  (EQ: reaches ~=~ reaches'), reaches = reaches'.
Proof.
  unfold incl. induction addrs; intros.
  - inversion RA. reflexivity.
  - (* Set up list equalities *)
    simpl in RA. einversion trivial reachables_incl as [reaches1 [FR2 Incl]].
    rewrite FR2 in RA. einstantiate trivial fold_right_reachables_incl.
    einstantiate trivial IHaddrs. split. assumption. destruct EQ.
    eapply incl_tran; eassumption. subst. destruct_reachables_at RA;

    (* Because this is the result of an ap, they should be trivially equal since
     * the resulting ap did not change anything *)
    (eapply set_ap_equiv_equal; [reflexivity|apply set_equiv_symm in EQ;
        assumption]).
Qed.

Definition reachables_hint_correct p h hints :=
  forall a_new addrs a0 s0 s2 n' a' s' x' q sz hints_res
    (Hints: hints a_new = Some hints_res)
    (NWC: forall s1 s2, p s1 = p s2)
    (XP0: exec_prog h (sub_prog p (a_new :: addrs)) a0 s0 n' s2 (Exit a_new))
    (LU: sub_prog p (a_new :: addrs) s2 a_new = Some (sz, q))
    (XS: exec_stmt h s2 q s' x')
    (EX: exitof (a_new + sz) x' = Exit a'),
    set_has hints_res a' = true.

Theorem reachables_at_complete: forall p h hints reaches reaches' s0 a0 n' s'
  a_new a' addrs
  (NWC: forall s1 s2, p s1 = p s2)
  (Init: set_has reaches a0 = true)
  (IHaddrs: forall s0 a0 n' s' a'
    (Init: set_has reaches a0 = true)
    (XP: exec_prog h (sub_prog p addrs) a0 s0 n' s' (Exit a')),
    set_has reaches a' = true)
  (HintsCorrect: reachables_hint_correct p h hints)
  (RA: reachables_at hints p a_new (Some reaches) = Some reaches')
  (EQ: reaches ~=~ reaches')
  (XP: exec_prog h (sub_prog p (a_new::addrs)) a0 s0 n' s' (Exit a')),
  set_has reaches' a' = true.
Proof.
  intros.

  (* Induct on n' *)
  apply exec_prog_equiv_exec_prog2 in XP.
  revert a' s' EQ XP. induction n'; intros; inversion XP; subst.
  - (* No execution *) destruct_reachables_at RA; apply set_ap_has_r; assumption.
  - (* Some executions *) clear XP. destruct (a1 == a_new).
    + (* When the last statement is at a_new *) destruct_reachables_at RA.
      * (* Use the hint's correctness *) apply set_ap_has_l.
        apply exec_prog_equiv_exec_prog2 in XP0.
        eapply HintsCorrect; try eassumption.
      * unfold sub_prog in LU0. destruct existsb; try discriminate.
        erewrite NWC in LU. erewrite LU in LU0. inversion LU0. subst.
        clear LU0 HintsCorrect IHn' IHaddrs. apply set_has_in.
        einstantiate trivial stmt_reachable_complete.
        destruct x' as [[a|n]|]; try inversion H; subst.
        -- (* Some exit *) apply set_has_in in H0. apply set_ap_left.
           destruct falls; [apply set_add_preserves|]; assumption.
        -- (* fallthru *) apply set_ap_left. apply set_add_correct.
    + (* IHn' tells us that a1 is already in the reaches set. Then we use IHaddrs
       * to tell us that the last statement will exit at a', which is reachable:
       *
       *        a0 ~~> a1 -> a'
       *        \------/\----/
       *          IHn'    IHaddrs
       *)
      einstantiate trivial IHn'. clear HintsCorrect.

      (* Doesn't matter if it's a hint or not, so we combine both cases using
       * one assert. *)
      assert (X: forall res, set_ap res reaches = reaches' ->
        set_has reaches' a' = true);
      [|destruct_reachables_at RA; eapply X; reflexivity].

      (* Then we just prove that our assertion is correct *)
      intros. subst. apply set_ap_has_r. eapply IHaddrs.

      (* Prove that a1 is already reachable *)
      erewrite <- set_equiv_has in H0 by eassumption. eassumption.

      (* Prove that we can execute from a1 ~> a' by saying we make one step *)
      eapply XStep; try eassumption; try constructor. clear IHn' IHaddrs.

      (* Prove that a1 is contained within addrs because a1 is in
       * (a_new::addrs) and a1 ≠ a_new. *)
      unfold sub_prog in *. destruct existsb eqn: InAddrs; try discriminate.
      apply existsb_iseqb_iff_in in InAddrs. inversion InAddrs; subst;
      [contradict n; reflexivity|]. rewrite <- existsb_iseqb_iff_in in H1.
      rewrite H1. assumption.
Qed.

Theorem expand_reachables_sub_complete: forall p h hints reaches s0 a0 s' n a'
  (Init: set_has reaches a0 = true) (NWC: forall s1 s2, p s1 = p s2)
  (HintsCorrect: reachables_hint_correct p h hints)
  (ER: expand_reachables hints p reaches = Some (reaches, false))
  (XP: exec_prog h (sub_prog p (set_elems reaches)) a0 s0 n s' (Exit a')),
  set_has reaches a' = true.
Proof.
  unfold expand_reachables. intros until reaches.
  remember (set_elems reaches) as addrs. clear Heqaddrs.
  revert reaches. induction addrs as [|a_new addrs]; intros.
  - (* nil *) inversion XP; subst. assumption. inversion LU.
  - (* non-nil *) simpl in ER. destruct reachables_at as [reaches'|] eqn: RA;
    try destruct set_equivb eqn: EQ; try discriminate.

    (* All reaches sets are all equivalent from our assumption *)
    apply set_equivb_iff_equiv in EQ.
    apply set_has_in, EQ, set_has_in in Init.
    apply set_has_in, EQ, set_has_in.
    einversion trivial reachables_incl as [reaches1 [RAnext Incl]].
    einstantiate trivial fold_right_reachables_incl as Incl2.
    einstantiate trivial (set_equiv_intro reaches1 reaches') as EQ2.
    destruct EQ. eapply incl_tran; eassumption. rewrite RAnext in RA.

    (* This is reachable because this is the return value of reachables_at *)
    eapply reachables_at_complete with (reaches:=reaches1); try eassumption.
    erewrite set_equiv_has by eassumption. assumption.

    (* First turn set_has reaches1 _ -> set_has reaches _ *)
    intros. apply set_equiv_symm in EQ as EQ3.
    erewrite set_equiv_has, set_equiv_has by eassumption.

    (*** Push the IHaddrs into the subproof ***)
    eapply IHaddrs; try eassumption.

    (* Show a1 is reachable using our initial reachables set *)
    erewrite set_equiv_has, <- set_equiv_has by eassumption. assumption.

    (* Assert that ER gives a value that is the same *)
    rewrite RAnext. destruct set_equivb eqn: EQB; try reflexivity.
    erewrite set_equivb_if_equiv in EQB. discriminate.
    apply set_equiv_symm in EQ2. eapply set_equiv_tran; eassumption.
Qed.

Theorem expand_reachables_complete: forall hints p h reaches n s0 a0 s' a'
  (Init: set_has reaches a0 = true) (NWC: forall s1 s2, p s1 = p s2)
  (HintsCorrect: reachables_hint_correct p h hints)
  (ER: expand_reachables hints p reaches = Some (reaches, false))
  (XP: exec_prog h p a0 s0 n s' (Exit a')),
  set_has reaches a' = true.
Proof.
  induction n; intros; inversion XP; subst.
  - assumption.
  - assert (set_has reaches a'0 = true);
      [|einstantiate trivial IHn as IHn; exact IHn].
    eapply expand_reachables_sub_complete; try eassumption.
    econstructor; try solve [eassumption|econstructor]. unfold sub_prog.
    destruct existsb eqn: EXB. eassumption.
    apply existsb_iseqb_iff_in_contra in EXB. apply set_has_in_contra in EXB.
    rewrite EXB in Init. discriminate.
Qed.

Theorem expand_reachables_equiv_equal: forall r1 r2 hints p
  (ER: expand_reachables hints p r1 = Some (r2, false)), r1 = r2.
Proof.
  intros. unfold expand_reachables in ER.
  destruct fold_right eqn: FR; try discriminate.
  destruct set_equivb eqn: SE; inversion ER. reflexivity.
Qed.

Theorem expand_reachables_n_complete: forall hints iter p h reaches n s0 a0 s' a'
  (Init: set_has reaches a0 = true) (NWC: forall s1 s2, p s1 = p s2)
  (HintsCorrect: reachables_hint_correct p h hints)
  (ER: expand_reachables_n hints p reaches iter = Some (reaches, false))
  (XP: exec_prog h p a0 s0 n s' (Exit a')),
  set_has reaches a' = true.
Proof.
  unfold expand_reachables_n, iterM. intros. revert ER XP.
  remember (fun _ => _) as fn. pattern (N.iter iter fn (Some (reaches, true))).
  apply N.iter_invariant; try discriminate. intros. subst.
  destruct x as [[r fin]|]; try discriminate.
  destruct fin; [|inversion ER; subst; apply H; [reflexivity|assumption]].
  erewrite (expand_reachables_equiv_equal r) in ER by eassumption.
  eapply expand_reachables_complete; try eassumption.
Qed.

Require Import Picinae_i386.
Require Import strchr_i386.
Import X86Notations.

Definition fh := htotal.

Definition ret_pres (esp0:N) (mem:addr->N) (s:store) :=
  exists mem1, s V_MEM32 = Ⓜ mem1 /\ mem Ⓓ[ esp0 ] = mem1 Ⓓ[ esp0 ].

Definition ret_invs (esp0:N) (mem:addr->N) (_:addr) (s:store) :=
  Some (ret_pres esp0 mem s).

Definition ret_post (esp0:N) (mem:addr->N) (_:exit) (s:store) :=
  ret_pres esp0 mem s.

Definition strchr_ret_invset esp0 mem :=
  invs (ret_invs esp0 mem) (ret_post esp0 mem).

Theorem strchr_welltyped: welltyped_prog x86typctx strchr_i386.
Proof.
  Picinae_typecheck.
Qed.

Ltac add_to_set s elem :=
  tryif is_var s then
    let v := lazymatch type of s with
             | list N => eval compute in (elem :: s)
             | set N  => eval compute in (elem :: set_elems s)
             | _      => eval compute in (elem :: nil)
             end in
    let vv := eval compute in (set_set (set_compact' v) (set_compact_nodup v)) in
    clear s; pose (s := vv)
  else
    let v := eval compute in (elem :: nil) in
    let vv := eval compute in (set_set (set_compact' v) (set_compact_nodup v)) in
    pose (s := vv).

Ltac compute_reaches' iters hint r XP0 :=
  lazymatch type of XP0 with
  | exec_prog ?h ?p ?a0 ?s0 _ _ _ =>
      let tmp := fresh "tmp" in
      let tmp_to_r := clear r; rename tmp into r in
      add_to_set r a0;
      lazymatch eval compute in (expand_reachables_n hint p r iters) with
      | Some (?s, ?changing) =>
          pose (tmp := set_compact s); compute in tmp; tmp_to_r;
          match changing with
          | true => idtac "expand_reachable not done!"
          | false =>
              let r_correct := fresh r "_correct" in
              assert (tmp: set_has r 0 = true); [reflexivity|];
              assert (r_correct: forall a' s' n, exec_prog h p a0 s0 n s' (Exit a') ->
                set_has r a' = true); [intros; eapply (expand_reachables_complete hint);
                  trivial2; instantiate; trivial2 | clear tmp]
          end
      | None => fail "expand_reachable failed"
      | _ => fail "Reachables not fully computable! Perhaps there are"
          "some symbolic variables"
      end
  | _ => idtac XP0 "expected of type exec_prog"
  end.

Ltac compute_reaches_fast iters hint r XP0 :=
  lazymatch type of XP0 with
  | exec_prog ?h ?p ?a0 ?s0 _ _ _ =>
      let tmp := fresh "tmp" in
      let tmp_to_r := clear r; rename tmp into r in
      add_to_set r a0;
      lazymatch eval compute in (expand_reachables_fast_n hint p (set_elems r, set_elems r) iters) with
      | Some (?s, ?frontier) =>
          match frontier with
          | nil => idtac
          | _ => idtac "expand_reachable_fast not done; Frontier:" frontier
          end;
          pose (tmp := set_compact' s); compute in tmp; tmp_to_r
      | None => fail "expand_reachable_fast failed"
      | _ => fail "Reachables not fully computable! Perhaps there are"
          "some symbolic variables"
      end
  | _ => idtac XP0 "expected of type exec_prog"
  end.

Ltac compute_reaches iters hint r XP0 :=
  compute_reaches_fast iters hint r XP0;
  compute_reaches' 1 hint r XP0.

Definition strchr_reachables_hint (a: addr): option (set addr) :=
  match a with
  | 401 => Some (@set_nil addr NEqDec)
  | _ => None
  end.

Compute expand_reachables_fast_n strchr_reachables_hint strchr_i386
          (0::nil, 0::nil) 300.

Theorem strchr_preserves_ret:
  forall s esp0 mem n s' x' (ESP0: s R_ESP = Ⓓ esp0)
         (MDL0: models x86typctx s)
         (MEM: forall s, s V_MEM32 = Ⓜ mem)
         (RET0: strchr_i386 s (mem Ⓓ[esp0]) = None)
         (XP0: exec_prog fh strchr_i386 0 s n s' x'),
         trueif_inv (strchr_ret_invset esp0 mem strchr_i386 x' s').
Proof.
  intros.


  (* Trivial base case *)
  assert (Trivial:
    trueif_inv (strchr_ret_invset esp0 mem strchr_i386 (Exit 0) s)).
    exists mem. split. apply MEM. reflexivity.
  clear ESP0.

  revert RET0 MDL0.

  time (compute_reaches 100 strchr_reachables_hint reachable XP0).



  pose (r := (set_add set_nil 0, true)).
  pose (tmp := eq_refl r).
  let x := (eval red in r) in
  match x with
  | (_, true) => idtac "HI"
  | _ => idtac "NO"
  end.
  apply r in tmp.
  rewrite r in tmp.

  end
      pose proof ()

  compute in r.

  (*  *)

  compute_reaches 30 hint mem mem.


  lazymatch type of XP0 with
  | exec_prog fh strchr_i386 0 s n s' x'
  pose (r := set)


  induction on invariant XP0; intros.

  apply Trivial.

  (* MDL0 *)
  eapply preservation_exec_prog. exact MDL0. exact strchr_welltyped. exact XP.

  compute in r.



Abort.


Definition init_store_delta (c: typctx): store_delta :=
  fun v =>
    match c v with
    | Some (NumT w) => Var v 0 w
    | Some (MemT _) | None => Complex
    end.

(*
N.iter
Definition trace_program (ct: N) (c: typctx) (vars: list var) (p: program)
  (entry: addr) (fn: store_delta -> stmt -> trace_state_res_with_prop):
  option trace_states_prop :=
  let tsp := (update ⊥ entry (init_store_delta c), [entry], ⊥)
  match ct with
  | 0 => Some tsp
  | n
 *)

Definition reachable_thru h p a0 s0 a1 a' := exists s' n0 n1 s1,
  exec_prog h p a0 s0 n0 s1 (Exit a1) /\ exec_prog h p a1 s1 n1 s' (Exit a').

Definition has_delta' (s s': store) (δ: store_delta) (P: var -> option Prop) :=
  forall v val (ESE: eval_simple_exp s (δ v) val) (PP: true_hyp P v), s' v = val.

(* For all address in the delta store map, either we are reachable through the
 * working set, or the delta_stores are in fact correct for all possible
 * executions *)
Definition state_correctness h p a0 s0 fδ working conds := forall a1,
  (Exists (fun w => reachable_thru h p a0 s0 w a1) working) \/
  (forall s1 n1 δ (XP1: exec_prog h p a0 s0 n1 s1 (Exit a1))
    (LUdelta: fδ a1 = Some δ), has_delta' s0 s1 δ conds).

Theorem has_delta'_weaken: forall s s' δ P1 P2
  (IMP: forall v, true_hyp P2 v -> true_hyp P1 v)
  (HD': has_delta' s s' δ P1), has_delta' s s' δ P2.
Proof.
  unfold has_delta'. intros. apply IMP in PP. eapply HD'; try eassumption.
Qed.

Lemma reachable_exec_prog: forall h p a0 s0 a1 a'
  (Reach: reachable_thru h p a0 s0 a1 a'),
  exists s' n0 n1, exec_prog h p a0 s0 (n0 + n1) s' (Exit a').
Proof.
  unfold reachable_thru. intros. destruct Reach as [s' [n0 [n1 [s1 [XP1 XP2]]]]].
  repeat eexists. eapply exec_prog_concat; eassumption.
Qed.

(* Temporarily admit this, so that we can destruct on whether a *)
Axiom middle_excluded: forall P, P \/ not P.

Theorem trace_program_step_preserved_stmt: forall q sz h ts_fn vars p a0 s0 a
  next_states st' fδ fδ' δ working working' conds P'
  (SS: incl st' next_states)
  (NWC: forall s1 s2, p s1 = p s2)
  (* TODO: something for domain_complete *)
  (LUa: fδ a = Some δ) (TSQ: ts_fn δ q = Some (next_states, P'))
  (PA: p null_state a = Some (sz, q))
  (TP: trace_program_step vars p (fδ, (a :: working), conds) ts_fn =
    Some (fδ', working', h_conj conds P'))
  (IHfδ: state_correctness h p a0 s0 fδ (a :: working) conds),
  state_correctness h p a0 s0 fδ' working' (h_conj conds P').
Proof.
  induction next_states; intros; simpl in TP; rewrite PA, LUa, TSQ in TP;
  remember (fold_left _ _ _) as res eqn: TP2; destruct res as [fδ1' new_working];
  inversion TP; subst; clear TP; simpl in TP2.
  - (* nil *) inversion TP2. subst. unfold state_correctness in *. intros.
    pose (reachable2 := fun a2 a1 => reachable_thru h p a0 s0 a1 a2).
    destruct (IHfδ a1) as [Working_a1|HD'_a1].
    (* Exists in a::working *)
    + rewrite app_nil_r. inversion Working_a1 as [? ? Reach_a1|];
      [|left; assumption]. subst. destruct Reach_a1 as
        [s_a1 [n_0a [n_a_a1 [s_a [XP_0a XP_a_a1]]]]].
      (* Contradiction between XP_a_a1 and PA and TSQ *)
      admit.
    + (* Already correct *) right. intros. eapply has_delta'_weaken;
      try eapply HD'_a1; try eassumption. intros. unfold h_conj, true_hyp in *.
      destruct (conds v), (P' v); try destruct H; solve [reflexivity|assumption].
  - 

    simpl in TP2.
Admitted.
 *)

Theorem trace_program_step_preserved: forall vars ts_fn p a0 s0 fδ fδ' h
  working working' conds conds' (NWC: forall s1 s2, p s1 = p s2)
  (* TODO: something for domain_complete *)
  (TP: trace_program_step vars p (fδ, working, conds) ts_fn =
    Some (fδ', working', conds'))
  (IHfδ: state_correctness h p a0 s0 fδ working conds),
  state_correctness h p a0 s0 fδ' working' conds'.
Proof.
  intros. destruct working.
  - (* nil *) unfold state_correctness in *. intros. inversion TP. subst.
    destruct (IHfδ a1); (left + right); assumption.
  - (* a :: working' *) simpl in TP.
    destruct (p _ a) eqn: PA; [|inversion TP]. (* Is it a valid program address *)
    destruct p0 as [sz q]. destruct (fδ a) eqn: LUa; [|inversion TP].
    destruct (ts_fn _ _) eqn: TSQ; [|inversion TP]. destruct p0 as [next_states P'].
    remember (fold_left _ _ _) as res eqn: TP2. destruct res as [fδ1' new_working].
    inversion TP. subst. clear TP. eapply trace_program_step_preserved_stmt;
    try eassumption. simpl. rewrite PA, LUa, TSQ.
    rewrite <- TP2. reflexivity.
Qed.


Definition trace_program_def vars p tsp :=
  trace_program vars p tsp (fun δ q =>
    match simple_trace_stmt δ q with
    | Some x => Some (x, ⊥)
    | None => None
    end).

Definition get_reg v (ts: trace_state_res) :=
  match ts with
  | None => nil
  | Some (paths, _) => map (fun '(δ, _) => δ v) paths
  end.
Require Import strchr_i386.
Require Import fstat_i386.

Definition simple_trace_stmt_at (p: program) (a: addr):
  option (N * list simple_exp) :=
  match p null_state a with
  | Some (sz, q) => Some (sz, get_reg R_ESP (simple_trace_stmt (fun v => VarOff v 0 32) q))
  | None => None
  end.

Fixpoint addrs (x:nat) :=
  match x with
  | O => 0 :: nil
  | S x' => N.of_nat x :: addrs x'
  end.

Compute rev (filter
  (fun x => match snd x with
            | Some _ => true
            | None => false
            end)
  (map (fun a => (a, simple_trace_stmt_at fstat_i386 a)) (addrs 450))).

(*
Lemma simplify_rep_stmt_red: forall q e h s s' x
  (EX: exec_stmt h s (Rep e q) s' x)
  (IHq : ∀ (s s' : store) (x : option exit) (EX : exec_stmt h s q s' x),
        exec_stack_oper h s q s' x EX (simplify_stmt q)),
  match simplify_stmt q with
  | SNop => x = None /\ s sp_reg = s' sp_reg
  | SOther => s sp_reg = s' sp_reg
  | _ => True
  end.
Proof.
  intros.
  inversion EX. subst. clear EX E w e. rewrite N2Nat.inj_iter in *.
  remember (N.to_nat n) as nn. clear n Heqnn. move nn at top. move IHq at top.
  repeat match goal with [H: _ |- _] => revert H end.
  induction nn; intros.
  - (* n = 0 *) inversion XS. subst. clear XS. destruct simplify_stmt;
    constructor; reflexivity.
  - (* n > 0 *) inversion XS; subst; clear XS.

    (* Terminated loop at this step *)
    specialize (IHq _ _ _ XS0).
    destruct simplify_stmt; try solve [constructor]; inversion IHq.
    discriminate. assumption.

    (* Continue onwards in the loop *)
    specialize (IHq _ _ _ XS1).
    specialize (IHnn _ _ _ XS0).
    destruct simplify_stmt; try solve [constructor]; inversion IHq.

    destruct IHnn. split. assumption.
    all: eapply eq_trans; eassumption.
Qed.
*)
Ltac fallthrus :=
  (left + right); reflexivity.

Theorem simplify_stmt_red_sp: forall q h s s' s1' x c0 c1 c' Xcond
  (XS: exec_stmt h s q s' x) (ESO: exec_stack_oper s s1' Xcond (simplify_stmt q))
  (STyp: hastyp_stmt c0 c1 q c'), Xcond x /\ s' sp_reg = s1' sp_reg.
Proof.
  induction q; intros; simpl in *;
  inversion STyp; subst; clear STyp.
  - (* Nop *) inversion XS. inversion ESO. subst. clear XS ESO. split.
    fallthrus. reflexivity.
  - (* Move *) inversion XS. split. inversion ESO; fallthrus. subst.
    destruct (sp_reg == v);
    [|constructor; [|reflexivity]; rewrite update_frame; [reflexivity|assumption]].
    (* Destruct on expression. For the error cases, anything happens, so ignore *)
    inversion E; subst; clear E; try constructor;
    inversion TE; subst; clear TE;
    inversion E1; subst; clear E1; try constructor;
    inversion T1; subst; clear T1;
    inversion E2; subst; clear E2; try constructor;
    inversion T2; subst; clear T2;
    destruct (sp_reg == v); try constructor;
    destruct bop; try constructor;
    subst; simpl in *.

    (* sp + n *)
    econstructor; solve [eassumption|reflexivity].
    (* sp - n *)
    econstructor; solve [eassumption|reflexivity].
    (* sp - n *)
    econstructor. eassumption. reflexivity. rewrite N.add_comm. reflexivity.
  - (* Jmp *) inversion XS. subst. constructor. reflexivity.
  - (* Exn *) inversion XS. subst. constructor. reflexivity.
  - (* Seq *) inversion XS; subst; destruct (simplify_stmt q1) eqn: SE1;
    destruct (simplify_stmt q2) eqn: SE2; try constructor; inversion XS; subst;
    try solve
      [ (* When we execute only the first statement, but it is SNop *)
        specialize (IHq1 _ _ _ _ _ _ _ XS0 TS1); inversion IHq1;
        discriminate
      | (* When we only execute the first statement, and it is SOther *)
        specialize (IHq1 _ _ _ _ _ _ _ XS0 TS1); inversion IHq1;
        assumption
      | (* When we execute both statements, and it is both SNop and SOther *)
        specialize (IHq1 _ _ _ _ _ _ _ XS1 TS1); inversion IHq1;
        specialize (IHq2 _ _ _ _ _ _ _ XS0 TS2); inversion IHq2;
        eapply eq_trans; eassumption
      | (* When we only execute the first statement, and it is arithmetic *)
        specialize (IHq1 _ _ _ _ _ _ _ XS0 TS1); inversion IHq1;
        econstructor; solve [eassumption|reflexivity]
      | (* When we execute both statements, either is arithmetic *)
        specialize (IHq1 _ _ _ _ _ _ _ XS1 TS1); inversion IHq1;
        specialize (IHq2 _ _ _ _ _ _ _ XS0 TS2); inversion IHq2;
        try first [rewrite <- SP_EQ in *|rewrite SP_EQ in *]; econstructor;
        solve [eassumption|reflexivity]
      ].
  - (* If *) inversion XS. subst. clear E. clear c' TE SS. destruct c;
    [ specialize (IHq2 _ _ _ _ _ _ _ XS TS2); rename IHq2 into IHq
    | specialize (IHq1 _ _ _ _ _ _ _ XS TS1); rename IHq1 into IHq];
    destruct (simplify_stmt q1) eqn: SE1; destruct (simplify_stmt q2) eqn: SE2;
    inversion IHq; subst; constructor; solve [reflexivity|assumption].
  - (* Rep *) assert (IHq2: ∀ (s s' : store) (x : option exit)
      (XS : exec_stmt h s q s' x), exec_stack_oper h s q s' x XS (simplify_stmt q)).
    intros. eapply IHq; eassumption.
    specialize (simplify_rep_stmt_semequiv _ _ _ _ _ _ XS IHq2) as Eq.

    destruct (simplify_stmt) eqn: CS; try constructor.
    destruct Eq. assumption. destruct Eq. assumption.
    assumption.
Qed.

Require Import Picinae_i386.
Require Import strchr_i386.
Definition null_state: store := fun _ => VaN 0 0.
Definition simplify_stmt_at (p: program) (a: addr): option (N * stack_oper) :=
  match p null_state a with
  | Some (sz, q) => Some (sz, simplify_stmt q)
  | None => None
  end.


Check filter.
Require Import fstat_i386.
Compute rev (filter
  (fun x => match snd x with
            | Some (_, SNop) => false
            | Some (_, SOther) => false
            | Some _ => true
            | None => false
            end)
  (map (fun a => (a, simplify_stmt_at fstat_i386 a)) (addrs 450))).


Fixpoint push_stack_offsets (p: program) (a: addr): option (set addr, ) :=
  match p null_state a with
  | Some (sz, q) =>
      match stmt_reachable q with
      | Some jmps =>
          fold_left
          set_add jmps (a + sz)
      | None => None
  | None => None.

Fixpoint get_reachable (p: program) (a: addr) :=
  get_jumps
