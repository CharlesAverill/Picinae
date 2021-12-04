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
Require Import Etacs.
Require Import Ntree.
Require Import Picinae_i386.
Require Import Coq.Program.Equality.

Open Scope bool.
Open Scope list.
Open Scope N.

Tactic Notation "vantisym" constr(v1) constr(v2) "by" tactic(T) :=
  vantisym v1 v2; [|solve [T]].

(* partial functions *)
Definition pfunc (A B:Type) := A -> option B.
Bind Scope pfunc_scope with pfunc.
Open Scope pfunc_scope.
Notation "x ⇀ y" := (pfunc x y) (at level 99, y at level 200, right associativity): type_scope.

(* the empty function (bottom) *)
Notation "⊥" := (fun _ => None).

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

Theorem Neqb_iseqb: forall a1 a2, (a1 =? a2) = iseqb a1 a2.
Proof.
  unfold iseqb. intros. destruct (a1 == a2);
  [apply N.eqb_eq|apply N.eqb_neq]; assumption.
Qed.

Theorem Neqb_iseqb_fn: N.eqb = iseqb.
Proof.
  apply functional_extensionality. intros. apply functional_extensionality.
  apply Neqb_iseqb.
Qed.

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

Definition set := treeN unit.
Declare Scope sets_scope.
Bind Scope sets_scope with set.

Definition set_nil: set := treeN_nil.
Definition set_elems: set -> list N := tkeys_n.
Definition set_has: set -> N -> bool := tcontains_n.

Definition set_add a (s: set): set := s [Ⓝ  a := tt ].
Arguments set_add: simpl never.
Notation "h ~:: t" := (set_add h t) (at level 60, right associativity):
  sets_scope.

Fixpoint set_add_all (s1: set) (l2: list N): set :=
  match l2 with
  | nil => s1
  | h::t => set_add h (set_add_all s1 t)
  end.

Definition set_ap (s1 s2: set): set :=
  set_add_all s1 (set_elems s2).
Arguments set_ap: simpl never.
Notation "s1 ~++ s2" := (set_ap s1 s2) (at level 60, right associativity):
  sets_scope.

Notation "{{ x }}" := (set_add x set_nil): sets_scope.
Notation "{{ x ; .. ; y ; z }}" :=
  (set_add x (.. (set_add y (set_add z set_nil)) .. )) : sets_scope.

Open Scope sets_scope.

Program Instance unit_EqDec: EqDec unit.
Next Obligation. decide equality. Defined.

Program Instance set_EqDec: EqDec set.
Next Obligation. decide equality; apply iseq. Defined.

Theorem set_has_in: forall a s, set_has s a = true <-> In a (set_elems s).
Proof.
  unfold set_has, set_elems. intros. rewrite <- tkeys_n_get.
  rewrite Neqb_iseqb_fn. apply existsb_iseqb_iff_in.
Qed.
Corollary set_has_in_contra: forall (s: set) a,
  set_has s a = false <-> ~In a (set_elems s).
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive set_has_in.
Qed.
Corollary set_elems_nodup: forall (s: set), NoDup (set_elems s).
Proof. apply tkeys_n_nodup. Qed.

Theorem set_elems_equiv_inj: forall s1 s2
  (EQV: list_equiv (set_elems s1) (set_elems s2)), s1 = s2.
Proof.
  intros. apply tkeys_n_inj, tkeys_n_equiv_equal; trivial2.

  (* Due to the degeneracy of the values used (units), all values are equal. *)
  unfold tcontains_n. intros. destruct tget_n, (tget_n s2); trivial2.
  destruct u, u0. reflexivity.
Qed.

Theorem set_add_idempotent: forall (s: set) a
  (InOld: In a (set_elems s)), a ~:: s = s.
Proof.
  unfold set_elems, set_add. intros. apply (existsb_iseqb_iff_in N) in InOld.
  rewrite <- Neqb_iseqb_fn, tkeys_n_get in InOld. apply tupdate_n_idempotent.
  unfold tcontains_n in InOld. destruct tget_n; [|discriminate].
  destruct u. reflexivity.
Qed.
Theorem set_add_preserves: forall (s: set) a1 a2
  (InOld: In a1 (set_elems s)), In a1 (set_elems (a2 ~:: s)).
Proof.
  intros. rewrite <- set_has_in in *. unfold set_add, set_has, tcontains_n in *.
  destruct (a1 == a2).
  - subst. rewrite tupdate_n_updated. reflexivity.
  - rewrite tupdate_n_frame; assumption.
Qed.
Theorem set_add_frame: forall (s: set) a1 a2
  (NEQ: a1 ≠ a2) (InAdd: In a1 (set_elems (a2 ~:: s))), In a1 (set_elems s).
Proof.
  intros. rewrite <- set_has_in in *. unfold set_add, set_has, tcontains_n in *.
  rewrite tupdate_n_frame in InAdd; assumption.
Qed.
Theorem set_add_correct: forall (s: set) a,
  In a (set_elems (a ~:: s)).
Proof.
  intros. rewrite <- set_has_in in *. unfold set_add, set_has, tcontains_n in *.
  rewrite tupdate_n_updated. reflexivity.
Qed.

Theorem set_ap_correct: forall (s1 s2: set) a,
  (In a (set_elems s1) \/ In a (set_elems s2)) <->
  In a (set_elems (s1 ~++ s2)).
Proof.
  unfold set_ap. intros. remember (set_elems s2) as l2. clear dependent s2. split.
  - (* -> *) intro In12. destruct In12 as [In1|In2]; simpl in *.
    + (* In1 *) revert In1. induction l2; intros.
      * (* nil *) assumption.
      * (* no nil *) simpl. apply set_add_preserves. apply IHl2. assumption.
    + (* In2 *) revert In2. induction l2; intros; inversion In2.
      * (* a = a0 *) subst. simpl. apply set_add_correct.
      * (* a in l *) simpl. apply set_add_preserves. apply IHl2; assumption.
  - (* <- *) intro InRes. revert l2 a InRes.
    induction l2; intros; simpl in InRes.
    + (* nil *) left. assumption.
    + (* no nil *) destruct (a0 == a); subst.
      * (* a = a0 *) right. left. reflexivity.
      * (* a ≠ a0 *) apply set_add_frame in InRes; [|assumption].
        einversion trivial IHl2 as [InL1|InL2].
        -- left. assumption.
        -- right. right. assumption.
Qed.
Corollary set_ap_left: forall (s1 s2: set) a
  (In1: In a (set_elems s1)), In a (set_elems (set_ap s1 s2)).
Proof. intros. apply set_ap_correct. left. assumption. Qed.
Corollary set_ap_right: forall (s1 s2: set) a
  (In2: In a (set_elems s2)), In a (set_elems (set_ap s1 s2)).
Proof. intros. apply set_ap_correct. right. assumption. Qed.
Corollary set_ap_incl_l: forall (s1 s2: set),
  incl (set_elems s1) (set_elems (set_ap s1 s2)).
Proof. unfold incl. intros. apply set_ap_left; assumption. Qed.
Corollary set_ap_incl_r: forall (s1 s2: set),
  incl (set_elems s2) (set_elems (set_ap s1 s2)).
Proof. unfold incl. intros. apply set_ap_right; assumption. Qed.
Theorem set_ap_has_split: forall (s1 s2: set) a,
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
Corollary set_ap_in_split: forall (s1 s2: set) a,
  In a (set_elems (set_ap s1 s2)) <-> In a (set_elems s1) \/ In a (set_elems s2).
Proof.
  (* Convert to set_has form *)
  split; intros In12; repeat rewrite <- set_has_in in *;
  [apply orb_prop; symmetry|apply orb_true_intro in In12];
  rewrite <- In12; apply set_ap_has_split.
Qed.
Corollary set_ap_has_l: forall (s1 s2: set) a
  (SH1: set_has s1 a = true), set_has (set_ap s1 s2) a = true.
Proof.
  intros. rewrite set_ap_has_split. rewrite SH1. apply orb_true_l.
Qed.
Corollary set_ap_has_r: forall (s1 s2: set) a
  (SH2: set_has s2 a = true), set_has (set_ap s1 s2) a = true.
Proof.
  intros. rewrite set_ap_has_split. rewrite SH2. apply orb_true_r.
Qed.
Corollary set_ap_has_contra_l: forall (s1 s2: set) a
  (SHres: set_has (set_ap s1 s2) a = false), set_has s1 a = false.
Proof.
  intros. rewrite set_ap_has_split in SHres. apply orb_false_elim in SHres.
  destruct SHres. assumption.
Qed.
Corollary set_ap_has_contra_r: forall (s1 s2: set) a
  (SHres: set_has (set_ap s1 s2) a = false), set_has s2 a = false.
Proof.
  intros. rewrite set_ap_has_split in SHres. apply orb_false_elim in SHres.
  destruct SHres. assumption.
Qed.

Lemma set_ap_elems_comm_equiv: forall s1 s2,
  list_equiv (set_elems (set_ap s1 s2)) (set_elems (set_ap s2 s1)).
Proof.
  intros. split; intros a InApp; repeat rewrite set_ap_in_split in *;
  apply or_comm; assumption.
Qed.

Theorem set_ap_refl: forall s1, s1 = set_ap s1 s1.
Proof.
  intros. apply set_elems_equiv_inj. split; intros a InApp;
  repeat rewrite set_ap_in_split in *; [left|destruct InApp]; assumption.
Qed.

Theorem set_ap_comm: forall s1 s2, set_ap s1 s2 = set_ap s2 s1.
Proof.
  intros. apply set_elems_equiv_inj. apply set_ap_elems_comm_equiv.
Qed.

Theorem set_ap_eclipse_l: forall s1 s2
  (Incl: incl (set_elems s1) (set_elems s2)),
  set_ap s1 s2 = s2.
Proof.
  intros. apply set_elems_equiv_inj. split.
  - intros a InAp. rewrite set_ap_in_split in InAp. destruct InAp; [|assumption].
    apply Incl. assumption.
  - apply set_ap_incl_r.
Qed.

Theorem set_ap_eclipse_r: forall s1 s2
  (Incl: incl (set_elems s2) (set_elems s1)),
  set_ap s1 s2 = s1.
Proof.
  intros. apply set_elems_equiv_inj. split.
  - intros a InAp. rewrite set_ap_in_split in InAp. destruct InAp. assumption.
    apply Incl. assumption.
  - apply set_ap_incl_l.
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

Theorem sub_prog_SS: forall p s al, (sub_prog p al s ⊆ p s).
Proof.
  unfold sub_prog. intros p s al a q SS.
  destruct existsb; [assumption|discriminate].
Qed.

Theorem sub_prog_incl_SS: forall p s al1 al2 (SS: incl al1 al2),
  (sub_prog p al1 s ⊆ sub_prog p al2 s).
Proof.
  intros. unfold sub_prog, pfsub. intros.
  destruct existsb eqn: EX1; try discriminate. rewrite H.
  destruct (existsb _ al2) eqn: EX2; try reflexivity.
  apply existsb_iseqb_iff_in in EX1. apply existsb_iseqb_iff_in_contra in EX2.
  contradict EX2. apply SS. assumption.
Qed.

Theorem sub_prog_nwc_pres: forall p al (NWC: forall s1 s2, p s1 = p s2),
  (forall s1 s2, sub_prog p al s1 = sub_prog p al s2).
Proof.
  intros. einstantiate NWC as NWC. apply functional_extensionality. intro a.
  eapply equal_f in NWC. unfold sub_prog. destruct existsb; [eassumption|reflexivity].
Qed.

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
              | None => Some (ts, changed)
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
  (reachable: set) (init_ts: trace_states): option (trace_states * bool) :=
  fold_right (trace_program_step_at vars p hints) (Some (init_ts, false))
    (set_elems reachable).

Definition iterM (n: N) {A} (f: A -> option A) (x: A) :=
  N.iter n (fun x => match x with Some x => f x | None => None end) (Some x).

Definition expand_trace_program_n (n: N)
  (hints: program -> addr -> trace_states -> option (trace_states * bool))
  (vars: list var) (p: program) (reachable: set) (init_ts: trace_states):
  option (trace_states * bool) :=
  N.iter n (fun x =>
    match x with
    | Some (ts, true) => expand_trace_program vars p hints reachable ts
    | Some (ts, false) => Some (ts, false)
    | None => None
    end) (Some (init_ts, true)).

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

(*
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
  intros until reachable. rename reachable into al.
  induction al; intros; unfold correctness_sub_prog; intros.
  - unfold sub_prog in XP. simpl in XP. inversion XP; subst.
    + apply Init. assumption.
    + inversion LU.
  - subst. unfold expand_trace_program in TPO. simpl in TPO.
    rewrite fold_expand_trace_program in TPO.
    eapply trace_program_step_at_steady_correct; try eassumption.
    eapply IHal; try eassumption. admit. (* trivial *)
    admit. (* trivial *)
    admit. (* trivial *)
Admitted.
 *)

Fixpoint stmt_reachable (s: stmt): option (set * bool) :=
  match s with
  | Nop => Some (set_nil, true)
  | Move _ _ => Some (set_nil, true)
  | Jmp e =>
      match e with
      | Word loc _ => Some ({{loc}}, false)
      | _ => None
      end
  | Exn _ => Some (set_nil, false)
  | Seq s1 s2 =>
      match (stmt_reachable s1, stmt_reachable s2) with
      | (Some (j1, false), _) => Some (j1, false)
      | (_, None) => None
      | (None, _) => None
      | (Some (j1, true), Some (j2, falls2)) => Some (j1 ~++ j2, falls2)
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

Definition reachables_at (hints: addr -> option set)
  (p: program) (a: addr) (accum: option set) :=
  match accum with
  | Some jmps =>
      match hints a with
      | Some jmps' => Some (jmps' ~++ jmps)
      | None =>
          match p null_state a with
          | Some (sz, q) =>
              match stmt_reachable q with
              | Some (sjmps, falls) => Some
                  (set_ap (if falls
                  then (a+sz) ~:: sjmps
                  else sjmps) jmps)
              | None => None
              end
          | None => None
          end
      end
  | None => None
  end.

Definition expand_reachables (hints: addr -> option set)
  (p: program) (reachable: set) :=
  match fold_right (reachables_at hints p) (Some reachable)
    (set_elems reachable) with
  | Some reachable' =>
      Some (if reachable == reachable'
      then (reachable, false)
      else (reachable', true))
  | None => None
  end.

Definition expand_reachables_fast (hints: addr -> option set)
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

Definition expand_reachables_n (hints: addr -> option set)
  (p: program) (reachable: set) (n: N) :=
  iterM n (fun x: (set * bool) => let '(x, b) := x in
    if b then expand_reachables hints p x else Some (x, false)) (reachable, true).

Definition expand_reachables_fast_n (hints: addr -> option set)
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
  - (* Jmp *) inversion E; subst; clear E; try discriminate; simpl in *.
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

Lemma reachables_incl: forall hints p a reaches' reaches
  (RA: reachables_at hints p a (Some reaches) = Some reaches'),
  incl (set_elems reaches) (set_elems reaches').
Proof.
  unfold reachables_at. intros. destruct hints eqn: Hints.
  - inversion RA. subst. intros a2 InS. apply set_ap_right. assumption.
  - destruct p as [[sz q]|] eqn: LU; try discriminate.
    destruct stmt_reachable as [[jmps falls]|] eqn: SRQ; try discriminate.
    inversion RA. subst. intros a2 InS. apply set_ap_right. assumption.
Qed.

Lemma fold_right_reachables_incl: forall hints p addrs reaches reaches'
  (RA: fold_right (reachables_at hints p) (Some reaches) addrs = Some reaches'),
  incl (set_elems reaches) (set_elems reaches').
Proof.
  unfold incl. induction addrs; intros.
  - inversion RA. subst. assumption.
  - simpl in RA. destruct fold_right eqn: FR; try discriminate.
    einstantiate trivial reachables_incl as Incl.
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
    (RA': set_ap (if falls then (a_new + sz) ~:: sjmps  else sjmps)
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

Definition reachables_hint_correct p h hints a0 s0 :=
  forall a_new addrs a1 s1 n a' s' x' q sz hints_res
    (Hints: hints a_new = Some hints_res)
    (NWC: forall s1 s2, p s1 = p s2)
    (XP: exec_prog h p a0 s0 n s1 (Exit a1))
    (LU: sub_prog p (a_new :: addrs) s1 a_new = Some (sz, q))
    (XS: exec_stmt h s1 q s' x')
    (EX: exitof (a_new + sz) x' = Exit a'),
    set_has hints_res a' = true.

Lemma expand_reachables_step: forall p h hints n addrs reaches s0 a0 s1 a1 s' a' x' q sz
  (Init: set_has reaches a1 = true)
  (NWC: forall s1 s2, p s1 = p s2) (HintsCorrect: reachables_hint_correct p h hints a0 s0)
  (FR: fold_right (reachables_at hints p) (Some reaches) addrs = Some reaches)
  (XP: exec_prog h p a0 s0 n s1 (Exit a1))
  (LU: sub_prog p addrs s1 a1 = Some (sz, q))
  (XS: exec_stmt h s1 q s' x') (EX: exitof (a1 + sz) x' = Exit a'),
  set_has reaches a' = true.
Proof.
  induction addrs as [|a_new addrs IHaddrs]; intros.
  - discriminate.
  - simpl in FR. destruct fold_right as [reaches'|] eqn: FR'; try discriminate.
    assert (reaches = reaches'). apply set_elems_equiv_inj. split.
      einstantiate trivial fold_right_reachables_incl.
      einstantiate trivial reachables_incl. subst.
    fold addr in a1. destruct (a1 == a_new) eqn: EQ; subst.
    + (* last statement at a_new *) destruct_reachables_at FR.
      * (* Provided by hint *) rewrite <- RA'. apply set_ap_has_l.
        eapply HintsCorrect; try eassumption.
      * (* Provided by our info *) erewrite sub_prog_nwc_pres in LU0 by assumption.
        erewrite sub_prog_SS in LU by eassumption. inversion LU. subst.
        einstantiate trivial stmt_reachable_complete. apply set_has_in.
        rewrite <- RA'. destruct x' as [[a|?]|]; try inversion EX; subst.
        -- (* Some exit *) apply set_has_in in H. apply set_ap_left.
           destruct falls; [apply set_add_preserves|]; assumption.
        -- (* fallthru *) apply set_ap_left. apply set_add_correct.
    + (* Already known, use IH *) simpl in LU.
      eapply IHaddrs; try eassumption. rewrite <- LU.
      unfold sub_prog, iseqb. simpl. rewrite EQ. reflexivity.
Qed.

Theorem expand_reachables_complete: forall hints p h n reaches s0 a0 s' a'
  (Init: set_has reaches a0 = true)
  (NWC: forall s1 s2, p s1 = p s2) (HintsCorrect: reachables_hint_correct p h hints a0 s0)
  (ER: expand_reachables hints p reaches = Some (reaches, false))
  (XP: exec_prog h p a0 s0 n s' (Exit a')),
  set_has reaches a' = true.
Proof.
  unfold expand_reachables. induction n; intros; fold addr in a0.
  - (* XP done *) inversion XP. subst. apply Init.
  - (* XP step *) apply exec_prog_equiv_exec_prog2 in XP. inversion XP. subst.
    apply exec_prog_equiv_exec_prog2 in XP0. assert (SH: set_has reaches a1 = true).
    eapply IHn; try eassumption. destruct fold_right eqn: FR; try discriminate.
    destruct (reaches == s); try discriminate. subst. rename s into reaches'.
    eapply expand_reachables_step; try eassumption.
    rewrite <- LU. unfold sub_prog. destruct existsb eqn: EXB; try reflexivity.
    rewrite existsb_iseqb_iff_in_contra in EXB. apply set_has_in in SH.
    contradiction EXB.
Qed.

Definition reachable_inv reaches :=
  invs (fun a _ => Some (set_has reaches a = true)) (fun _ _ => True).

Theorem expand_reachables_complete_inv: forall hints p h s0 a0 n reaches s' a'
  (Init: set_has reaches a0 = true)
  (NWC: forall s1 s2, p s1 = p s2) (HintsCorrect: reachables_hint_correct p h hints a0 s0)
  (ER: expand_reachables hints p reaches = Some (reaches, false))
  (XP: exec_prog h p a0 s0 n s' (Exit a')),
  trueif_inv (reachable_inv reaches p (Exit a') s').
Proof.
  intros. unfold trueif_inv, reachable_inv, invs.
  destruct p; try reflexivity. eapply expand_reachables_complete; eassumption.
Qed.

Theorem expand_reachables_equiv_equal: forall r1 r2 hints p
  (ER: expand_reachables hints p r1 = Some (r2, false)), r1 = r2.
Proof.
  intros. unfold expand_reachables in ER.
  destruct fold_right eqn: FR; try discriminate.
  destruct (r1 == s); inversion ER. reflexivity.
Qed.

Theorem expand_reachables_n_complete_inv: forall hints iter p h reaches n s0 a0 s' a'
  (Init: set_has reaches a0 = true)
  (NWC: forall s1 s2, p s1 = p s2) (HintsCorrect: reachables_hint_correct p h hints a0 s0)
  (ER: expand_reachables_n hints p reaches iter = Some (reaches, false))
  (XP: exec_prog h p a0 s0 n s' (Exit a')),
  trueif_inv (reachable_inv reaches p (Exit a') s').
Proof.
  unfold expand_reachables_n, iterM. intros. revert ER XP.
  remember (fun _ => _) as fn. pattern (N.iter iter fn (Some (reaches, true))).
  apply N.iter_invariant; try discriminate. intros. subst.
  destruct x as [[r fin]|]; try discriminate.
  destruct fin; [|inversion ER; subst; apply H; trivial2].
  erewrite (expand_reachables_equiv_equal r) in ER by eassumption.
  eapply expand_reachables_complete_inv; try eassumption.
Qed.

Ltac add_to_set s elem :=
  tryif is_var s then
    let tmp := eval compute in s in
    clear s; pose (s := elem ~:: tmp); compute in s
  else
    pose (s := {{elem}}).

Ltac compute_reaches' iters hint r XP0 :=
  lazymatch type of XP0 with
  | exec_prog ?h ?p ?a0 ?s0 _ _ _ =>
      add_to_set r a0;
      lazymatch eval compute in (expand_reachables_n hint p r iters) with
      | Some (?s, ?changing) =>
          clear r; pose (r := s);
          match changing with
          | true => idtac "expand_reachable not done!"
          | false =>
              let tmp1 := fresh r "_correct" in
              let tmp2 := fresh in
              let tmp3 := fresh in
              assert (tmp1: set_has r 0 = true); [reflexivity|];
              assert (tmp2: r = nodup iseq r); [reflexivity|];
              assert (tmp3: NoDup r); [rewrite tmp2; apply NoDup_nodup|];
              invariant (expand_reachables_complete_inv hint p h s0 a0) from tmp1;
                try reflexivity; try eassumption; clear tmp2 tmp3
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
          clear r; pose (r := s); compute in r
      | None => fail "expand_reachable_fast failed"
      | ?res => idtac "Reachables not fully computable! Perhaps there are"
          "some symbolic variables:";
          idtac res
      end
  | _ => idtac XP0 "expected of type exec_prog"
  end.

Ltac compute_reaches iters hint r XP0 :=
  compute_reaches_fast iters hint r XP0;
  compute_reaches' 1 hint r XP0.

Theorem welltyped_prog_sub: forall p a c (WT: welltyped_prog c p),
  welltyped_prog c (sub_prog p a).
Proof.
  intros. unfold welltyped_prog. intros.
  destruct sub_prog as [[sz q]|] eqn: SUB; try reflexivity.
  specialize (WT s a0) as WT. unfold sub_prog in SUB.
  destruct existsb; try discriminate. rewrite SUB in WT. assumption.
Qed.

Require Import Picinae_i386.
Require Import strchr_i386.
Require Import test.
Import X86Notations.

Definition compactify_delta (δ: store_delta): store_delta :=
  fun (v: var) =>
    match v with
    | V_MEM32 => δ V_MEM32
    (* Flags (1-bit registers): *)
    | R_AF => δ R_AF
    | R_CF => δ R_CF
    | R_DF => δ R_DF
    | R_OF => δ R_OF
    | R_PF => δ R_PF
    | R_SF => δ R_SF
    | R_ZF => δ R_ZF
    (* Segment selectors (16-bit registers): *)
    | R_CS => δ R_CS
    | R_DS => δ R_DS
    | R_ES => δ R_ES
    | R_FS => δ R_FS
    | R_GS => δ R_GS
    | R_SS => δ R_SS
    (* Floating point control register (16-bit): *)
    | R_FPU_CONTROL => δ R_FPU_CONTROL (* NumT 16 *)
    (* Floating point registers (80-bit): *)
    | R_ST0 => δ R_ST0
    | R_ST1 => δ R_ST1
    | R_ST2 => δ R_ST2
    | R_ST3 => δ R_ST3
    | R_ST4 => δ R_ST4
    | R_ST5 => δ R_ST5
    | R_ST6 => δ R_ST6
    | R_ST7 => δ R_ST7 (* NumT 80 *)
    (* General-purpose registers (32-bit): *)
    | R_EAX => δ R_EAX
    | R_EBX => δ R_EBX
    | R_ECX => δ R_ECX
    | R_EDX => δ R_EDX
    | R_EDI => δ R_EDI
    | R_ESI => δ R_ESI
    (* Stack pointer and base pointer (32-bit): *)
    | R_ESP => δ R_ESP
    | R_EBP => δ R_EBP
    (* Modifiable segment base registers (32-bit): *)
    | R_FS_BASE => δ R_FS_BASE
    | R_GS_BASE => δ R_GS_BASE
    (* Descriptor table registers (32-bit): *)
    | R_LDTR => δ R_LDTR
    | R_GDTR => δ R_GDTR
    (* SSE control register (32-bit): *)
    | R_MXCSR => δ R_MXCSR (* NumT 32 *)
    (* MMX and SSE registers (256-bit): *)
    | R_YMM0 => δ R_YMM0
    | R_YMM1 => δ R_YMM1
    | R_YMM2 => δ R_YMM2
    | R_YMM3 => δ R_YMM3
    | R_YMM4 => δ R_YMM4
    | R_YMM5 => δ R_YMM5
    | R_YMM6 => δ R_YMM6
    | R_YMM7 => δ R_YMM7
    | R_YMM8 => δ R_YMM8
    | R_YMM9 => δ R_YMM9
    | R_YMM10 => δ R_YMM10
    | R_YMM11 => δ R_YMM11
    | R_YMM12 => δ R_YMM12
    | R_YMM13 => δ R_YMM13
    | R_YMM14 => δ R_YMM14
    | R_YMM15 => δ R_YMM15
    (* These meta-variables model page access permissions: *)
    | A_READ => δ A_READ
    | A_WRITE => δ A_WRITE
    | V_TEMP n => δ (V_TEMP n)
    end.

Definition fh := htotal.

Definition init_store_delta: store_delta :=
  fun v => Some (Var v).

Definition vars := R_EBP :: R_ESP :: nil.

Definition simp_prog: program := fun _ a =>
  match a with

  (* 0x1: movl %esp, %ebp *)
  | 0 => Some (1,
      Move R_EBP (Var R_ESP)
  )
  | 1 => Some (1, Jmp (Word a 32))
  | _ => None
  end.

Theorem simp_prog_welltyped: welltyped_prog x86typctx simp_prog.
Proof.
  Picinae_typecheck.
Qed.

Definition simp_prog_trace_hint (p: program) (a: addr) (ts: trace_states):
  option (trace_states * bool) := None.

Definition simp_prog_trace reachables := expand_trace_program_n 10
  simp_prog_trace_hint vars simp_prog reachables (update ⊥ 0 (Some init_store_delta)).

Goal True.
Proof.

  pose (x := match simp_prog_trace {{0;1}} with
             | Some (ts, b) =>
                 match ts 1 with
                 | Some δ => Some (compactify_delta δ, b)
                 | None => None
                 end
             | None => None
             end).
  compute in x.
Abort.



Theorem my_prog_welltyped: welltyped_prog x86typctx my_prog.
Proof.
  Picinae_typecheck.
Qed.

Definition my_prog_reachables_hint (ret: addr) (a: addr): option (set addr) :=
  match a with
  | 34 => Some (ret::nil)
  | _ => None
  end.

Definition my_prog_reachables ret := expand_reachables_fast_n
  (my_prog_reachables_hint ret) my_prog (0 :: nil, 0 :: nil) 100.

Definition my_prog_trace_hint (p: program) (a: addr) (ts: trace_states):
  option (trace_states * bool) :=
  match a with
  | 34 => Some (ts, false)
  | _ => None
  end.

Definition my_prog_trace reachables := expand_trace_program_n 10
  my_prog_trace_hint vars my_prog reachables (update ⊥ 0 (Some init_store_delta)).

Goal True.
Proof.

  pose (x := my_prog_reachables 0).
  compute in x.
  match eval compute in x with
  | Some (?v, nil) => clear x; pose (reachables := v)
  end.
  pose (x := match my_prog_trace reachables with
             | Some (ts, b) =>
                 match ts 34 with
                 | Some δ => Some (compactify_delta δ, b)
                 | None => None
                 end
             | None => None
             end).
  compute in x.
Abort.

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



Definition strchr_reachables_hint (ret: addr) (a: addr): option (set addr) :=
  match a with
  | 401 => Some (ret::nil)
  | _ => None
  end.

Definition strchr_reachables ret := expand_reachables_fast_n
  (strchr_reachables_hint ret) strchr_i386 (0 :: nil, 0 :: nil) 100.

Definition strchr_trace_hint (p: program) (a: addr) (ts: trace_states):
  option (trace_states * bool) :=
  match a with
  | 401 => Some (ts, false)
  | _ => None
  end.

Definition strchr_trace reachables := expand_trace_program_n 1
  strchr_trace_hint vars strchr_i386 reachables (update ⊥ 0 (Some init_store_delta)).

Goal True.
Proof.
  idtac "DOING STRCHR_TRACE".

  pose (x := strchr_reachables 0).
  compute in x.
  match eval compute in x with
  | Some (?v, nil) => clear x; pose (reachables := v)
  end.
  pose (x := match strchr_trace reachables with
             | Some (ts, b) =>
                 match ts 401 with
                 | Some δ => Some (compactify_delta δ, b)
                 | None => None
                 end
             | None => None
             end).
  time (vm_compute in x).
  idtac "DONE COMPUTATION".
  match eval red in x with ?v => idtac v end.

  match eval red in x with
  | Some (?v, true) => idtac "STILL MORE"; clear x; pose (x := v)
  | Some (?v, false) => clear x; pose (x := v)
  end.
Abort.

  pose (vv2 := x V_MEM32). compute in vv2.





Compute
  match strchr_trace 1 with
  | Some (ts, b) => Some (ts 401, b)
  | None => None
  end.


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

  (* TODO: this 0 should actually be some symbolic value (optimally)! *)
  compute_reaches 100 (strchr_reachables_hint 0) reachable XP0.

  (* Prove that the hint that we give is valid. *)
  unfold reachables_hint_correct. intros.
  destruct a_new as [|a]; repeat first [ discriminate | destruct a as [a|a|]].
  compute in LU. inversion LU. subst. clear dependent reachable.
  inversion Hints. subst. einstantiate trivial preservation_exec_prog as MDL.
  exact strchr_welltyped. step_stmt XS. destruct XS as [[ST' EX'] [? _]]. subst.
  inversion EX. subst. unsimpl (getmem LittleE 4 _ _). clear EX.
  (* Here we show that the return value is preserved!! *) admit.

  revert RET0 MDL0.
  induction on invariant XP0; intros.

  apply Trivial.

  (* MDL0 *)
  eapply preservation_exec_prog. exact MDL0. exact strchr_welltyped. exact XP.

  destruct_inv 32 PRE.

Abort.


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
