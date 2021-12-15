Require Import Etacs.
Require Import FunctionalExtensionality.
Require Import Picinae_theory.
Require Import Arith.
Require Import NArith.
Require Import List.
Require Import Bool.

Open Scope N.

(* Some functions stuff *)
Definition ident {A} (a: A): A := a.
Definition compose {A} {B} {C} (fn1: B -> C) (fn2: A -> B) (a: A): C := fn1 (fn2 a).
Definition injective {A} {B} (fn: A -> B) :=
  forall p1 p2 (EQ: fn p1 = fn p2), p1 = p2.

Ltac prove_injective :=
  match goal with
  | [|- injective _] =>
      let p1 := fresh "p1" in
      let p2 := fresh "p2" in
      let EQ := fresh "EQ" in
      intros p1 p2 EQ; repeat first
        [ match type of EQ with
          | ?fn _ = _ =>
              match goal with
              | INJ: injective fn |- _ => apply INJ in EQ
              | _ => injection EQ; clear EQ; intros EQ
              end
          end
        | trivial2
        ]
  end.


Theorem compose_ident_l: forall A B (fn: A -> B), compose ident fn = fn.
Proof.
  intros. erewrite functional_extensionality. reflexivity.
  intros. unfold compose, ident. reflexivity.
Qed.

Theorem compose_ident_r: forall A B (fn: A -> B), compose fn ident = fn.
Proof.
  intros. erewrite functional_extensionality. reflexivity.
  intros. unfold compose, ident. reflexivity.
Qed.

Theorem injective_contra: forall A B (fn: A -> B) p1 p2 (INJ: injective fn)
  (NEQ: p1 <> p2), fn p1 <> fn p2.
Proof.
  intros. revert NEQ. contrapositive INJ.
Qed.

(* Some lists stuff and related theorems *)
Definition is_empty {A} (l: list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Theorem NoDup_app: forall A (l l': list A) (ND1: NoDup l) (ND2: NoDup l')
  (CrossNE: forall a b (InL: In a l) (InL': In b l'), a <> b),
  NoDup (l ++ l').
Proof.
  induction l; intros.
  - assumption.
  - inversion ND1. subst. clear ND1. constructor; fold (app l).

    (* a cannot be in l or l' *)
    intros Contra. apply in_app_or in Contra. destruct Contra. tauto.
    einstantiate CrossNE. constructor. reflexivity. eassumption. invalid H0.

    (* IH *)
    apply IHl; try eassumption. intros. apply CrossNE; try right; assumption.
Qed.

Theorem in_map_inj_iff: forall A B (f: A -> B) l x (INJ: injective f),
  In (f x) (map f l) <-> In x l.
Proof.
  intros. split; [|apply in_map]. intros InMl. apply in_map_iff in InMl.
  destruct InMl as [x' [EQ In]]. apply INJ in EQ. subst. assumption.
Qed.

Lemma NoDup_map_inj: forall (A B : Type) (f : A -> B) (l : list A)
  (INJ: injective f) (ND: NoDup l), NoDup (map f l).
Proof.
  induction l; intros.
  - constructor.
  - simpl. inversion ND. subst. constructor.

    (* f a is not in map *)
    intro Contra. apply in_map_inj_iff in Contra. contradiction H1.
    prove_injective.

    (* NoDup of map *)
    apply IHl; assumption.
Qed.

Theorem map_inj: forall (A B : Type) (f : A -> B)
  (INJ: injective f), injective (map f).
Proof.
  intros. prove_injective. revert p2 EQ. induction p1; intros.
  - destruct p2; [|discriminate]. reflexivity.
  - destruct p2. discriminate. simpl in EQ. inversion EQ. apply INJ in H0.
    subst. f_equal. apply IHp1. assumption.
Qed.

Definition list_equiv {A} (l1 l2: list A) := incl l1 l2 /\ incl l2 l1.
Theorem list_nequiv_1: forall A (h: A) t, list_equiv nil (h::t) -> False.
Proof. intros. destruct H. einversion (H0 h). left. reflexivity. Qed.

Theorem list_nequiv_2: forall A (h: A) t, list_equiv (h::t) nil -> False.
Proof. intros. destruct H. einversion (H h). left. reflexivity. Qed.

Theorem list_equiv_refl: forall A (l: list A), list_equiv l l.
Proof. intros. split; apply incl_refl. Qed.

Theorem list_equiv_symm: forall A (l1 l2: list A),
  list_equiv l1 l2 <-> list_equiv l2 l1.
Proof. intros. split; intros [? ?]; split; assumption. Qed.

Theorem list_equiv_tran: forall A (l1 l2 l3: list A),
  list_equiv l1 l2 -> list_equiv l2 l3 -> list_equiv l1 l3.
Proof.
  intros A l1 l2 l3 [Incl12 Incl21] [Incl23 Incl32].
  split; eapply incl_tran; eassumption.
Qed.

Theorem incl_cons_2: forall {A} {a : A} {l m : list A},
  In a l -> incl l m -> incl (a :: l) m.
Proof. intros. intros a0 InA. inversion InA; subst; apply H0; assumption. Qed.

Theorem incl_map_iff: forall {A B} (f: A -> B) {l1 l2: list A}
  (INJ: injective f), incl l1 l2 <-> incl (map f l1) (map f l2).
Proof.
  split. apply incl_map. intros Incl a In1. specialize (Incl (f a)).
  eapply in_map_inj_iff, Incl, in_map_inj_iff; assumption.
Qed.

Theorem list_equiv_map_iff: forall {A B} (f: A -> B) {l1 l2: list A}
  (INJ: injective f), list_equiv l1 l2 <-> list_equiv (map f l1) (map f l2).
Proof.
  split; intros EQV; destruct EQV as [EQV1 EQV2];
  split; (erewrite <- incl_map_iff + erewrite incl_map_iff); eassumption.
Qed.

Theorem list_equiv_cons: forall {A} {l1 l2} (a: A) (In1: In a l1),
  list_equiv l1 l2 <-> list_equiv (a::l1) l2.
Proof.
  split; intros EQV.
  - destruct EQV as [Incl12 Incl21]. split; [apply incl_cons_2|apply incl_tl];
    assumption.
  - destruct EQV as [Incl12 Incl21]. split.
    + intros a' In1'. apply Incl12. right. assumption.
    + intros a' In2'. einstantiate trivial (Incl21 a') as In1'.
      inversion In1'; subst; assumption.
Qed.

Theorem list_equiv_remove: forall {A} (a: A) {e: EqDec A} l1 l2
  (EQV: list_equiv l1 l2), list_equiv (remove iseq a l1) (remove iseq a l2).
Proof. intros. destruct EQV. split; apply remove_incl; assumption. Qed.

Theorem list_equiv_remove_inv: forall {A} (a: A) {e: EqDec A} l1 l2
  (In1: In a l1) (In2: In a l2)
  (EQV: list_equiv (remove iseq a l1) (remove iseq a l2)), list_equiv l1 l2.
Proof.
  intros. destruct EQV. split; intros a' In'; destruct (a' == a); subst; trivial2;
  ((einstantiate (H a') + einstantiate (H0 a'));
  [apply in_in_remove|eapply in_remove]; eassumption).
Qed.

Theorem list_equiv_partition: forall A {e: EqDec A} (l1_1 l1_2 l2_1 l2_2: list A)
  (EQV: list_equiv (l1_1 ++ l1_2) (l2_1 ++ l2_2))
  (DISJ1: forall a b (In1: In a l1_1) (In2: In b l2_2), a <> b)
  (DISJ2: forall a b (In1: In a l2_1) (In2: In b l1_2), a <> b),
  list_equiv l1_1 l2_1 /\ list_equiv l1_2 l2_2.
Proof.
  induction l1_1; intros.
  - destruct l2_1. split; [apply list_equiv_refl|trivial2].
    simpl in *. destruct EQV as [_ Contra].
    destruct (DISJ2 a a). left. reflexivity. apply Contra. left. reflexivity.
    reflexivity.
  - destruct (in_dec iseq a l1_1).
    + (* a is still in l1_1 *) simpl in EQV. rewrite <- list_equiv_cons in EQV;
      [|apply in_or_app; left; assumption]. einstantiate trivial IHl1_1.
      intros. apply DISJ1; [right|]; assumption.
      rewrite <- list_equiv_cons; assumption.
    + (* a no longer is in l1_1. a must only be in l2_1 *)
      assert (N2_2: ~ In a l2_2).
        intro In22. edestruct (DISJ1 a a); trivial2. left. reflexivity.
      assert (In21: In a l2_1). destruct EQV. einstantiate (H a) as In.
        left. reflexivity. apply in_app_or in In. destruct In. assumption.
        contradiction N2_2.
      assert (N1_2: ~ In a l1_2). intro In12. edestruct (DISJ2 a a); trivial2.

      apply (list_equiv_remove a) in EQV as EQV2.
      simpl in EQV2. vreflexivity a. repeat rewrite remove_app in EQV2.
      rewrite notin_remove in EQV2 by assumption.
      einstantiate trivial IHl1_1 as IHl1_1.
      (* DISJ1' *)
      intros. apply DISJ1. right. assumption. eapply in_remove; eassumption.
      (* DISJ2' *)
      intros. apply DISJ2; eapply in_remove; eassumption.

      (* From a remove operation, we show they are equivalent *)
      destruct IHl1_1 as [EQV_1 EQV_2].
      repeat rewrite notin_remove in EQV_2 by assumption. split; [|assumption].
      eapply list_equiv_remove_inv; try left; trivial2.
      simpl. vreflexivity a. rewrite notin_remove; assumption.
Qed.

Theorem list_app_partition: forall A (l1_1 l1_2 l2_1 l2_2: list A)
  (EQ: (l1_1 ++ l1_2) = (l2_1 ++ l2_2))
  (DISJ1: forall a b (In1: In a l1_1) (In2: In b l2_2), a <> b)
  (DISJ2: forall a b (In1: In a l2_1) (In2: In b l1_2), a <> b),
  l1_1 = l2_1 /\ l1_2 = l2_2.
Proof.
  induction l1_1; intros.
  - destruct l2_1. split; trivial2. simpl in *. subst.
    destruct (DISJ2 a a); try left; reflexivity.
  - destruct l2_1. simpl in *. subst. destruct (DISJ1 a a); try left; reflexivity.
    simpl in EQ. inversion EQ. subst. einstantiate trivial IHl1_1 as IHl1_1.
    (* DISJ1' *) intros. apply DISJ1; try right; assumption.
    (* DISJ2' *) intros. apply DISJ2; try right; assumption.
    destruct IHl1_1 as [EQ1 EQ2]. subst. split; reflexivity.
Qed.


Inductive treeP_ (V: Type) :=
  | TPleaf (val: V)
  | TP0 (t0: treeP_ V) (val: option V)
  | TP1 (t1: treeP_ V) (val: option V)
  | TP01 (t0 t1: treeP_ V) (val: option V).

Definition treeP V := option (treeP_ V).
Definition treeP_nil {V}: treeP V := None.

Arguments TPleaf {_} _.
Arguments TP0 {_} _ _.
Arguments TP1 {_} _ _.
Arguments TP01 {_} _ _ _.

Inductive treeN (V: Type) :=
  | TN (v0: option V) (tp: treeP V).
Arguments TN {_} _ _.

Definition treeN_nil {V}: treeN V := TN None treeP_nil.

Instance positive_EqDec: EqDec positive :=
  { iseq := Pos.eq_dec }.

Program Instance option_EqDec A `(e: EqDec A): EqDec (option A).
Next Obligation. decide equality. apply iseq. Defined.

Program Instance treeP__EqDec V `(e: EqDec V): EqDec (treeP_ V).
Next Obligation. decide equality; apply iseq. Defined.

Program Instance treeP_EqDec V `(e: EqDec V): EqDec (treeP V).
Next Obligation. decide equality; apply iseq. Defined.

Program Instance treeN_EqDec V `(e: EqDec V): EqDec (treeN V).
Next Obligation. decide equality; apply iseq. Defined.

Definition tempty_p {V} (t: treeP V) :=
  match t with
  | Some _ => false
  | None => true
  end.

Definition tempty_n {V} (t: treeN V) :=
  match t with
  | TN (Some _) _ => false
  | TN None tp => tempty_p tp
  end.

Definition textract_node_p {V} (t: treeP V): (treeP V * treeP V * option V) :=
  match t with
  | Some t =>
      match t with
      | TPleaf v =>  (None, None, Some v)
      | TP0 t0 ov => (Some t0, None, ov)
      | TP1 t1 ov => (None, Some t1, ov)
      | TP01 t0 t1 ov => (Some t0, Some t1, ov)
      end
  | None => (None, None, None)
  end.

Definition tupdate_node_p {V} (t0: treeP V) (t1: treeP V) (ov: option V): treeP V :=
  match t0, t1 with
  | None, None =>
      match ov with
      | None => None
      | Some v => Some (TPleaf v)
      end
  | Some t0, None => Some (TP0 t0 ov)
  | None, Some t1 => Some (TP1 t1 ov)
  | Some t0, Some t1 => Some (TP01 t0 t1 ov)
  end.

Fixpoint tget_p {V} (t: treeP V) (key: positive) {struct key}: option V :=
  let '(t0, t1, ov) := textract_node_p t in
  match key with
  | xO key' => tget_p t0 key'
  | xI key' => tget_p t1 key'
  | xH => ov
  end.

Definition tget_n {V} (t: treeN V) (key: N): option V :=
  match t with
  | TN ov tp =>
      match key with
      | N0 => ov
      | Npos key' => tget_p tp key'
      end
  end.

Definition tcontains_p {V} (t: treeP V) (key: positive): bool :=
  match tget_p t key with
  | Some _ => true
  | None => false
  end.

Definition tcontains_n {V} (t: treeN V) (key: N): bool :=
  match tget_n t key with
  | Some _ => true
  | None => false
  end.

Fixpoint tupdate_p {V} (t: treeP V) (key: positive) (val: V): treeP V :=
  let '(t0, t1, ov) := textract_node_p t in
  match key with
  | xO key' => tupdate_node_p (tupdate_p t0 key' val) t1 ov
  | xI key' => tupdate_node_p t0 (tupdate_p t1 key' val) ov
  | xH => tupdate_node_p t0 t1 (Some val)
  end.

Definition tupdate_n {V} (t: treeN V) (key: N) (val: V): treeN V :=
  match t with
  | TN ov tp =>
      match key with
      | N0 => TN (Some val) tp
      | Npos key' => TN ov (tupdate_p tp key' val)
      end
  end.

Notation "t [Ⓝ  x := y ]" := (tupdate_n t x y) (at level 50, left associativity).
Notation "t [Ⓟ  x := y ]" := (tupdate_p t x y) (at level 50, left associativity).
Notation "t Ⓝ[ x ]" := (tget_n t x) (at level 10).
Notation "t Ⓟ[ x ]" := (tget_p t x) (at level 10).

Fixpoint tkeys_p_ {V} (t: treeP_ V) (fn: positive -> positive): list positive :=
  let fn0 := compose fn xO in
  let fn1 := compose fn xI in
  match t with
  | TPleaf v => (fn xH) :: nil
  | TP0 t0 ov =>
      match ov with
      | Some v => fn xH :: nil
      | None => nil
      end ++ tkeys_p_ t0 fn0
  | TP1 t1 ov =>
      match ov with
      | Some v => fn xH :: nil
      | None => nil
      end ++ tkeys_p_ t1 fn1
  | TP01 t0 t1 ov =>
      match ov with
      | Some v => fn xH :: nil
      | None => nil
      end ++ tkeys_p_ t0 fn0 ++ tkeys_p_ t1 fn1
  end.

Definition tkeys_p {V} (t: treeP V) (fn: positive -> positive): list positive :=
  match t with
  | Some t => tkeys_p_ t fn
  | None => nil
  end.

Definition tkeys_n {V} (t: treeN V): list N :=
  match t with
  | TN v0 tp =>
      match v0 with
      | None => nil
      | Some v => 0 :: nil
      end ++ map Npos (tkeys_p tp ident)
  end.

Theorem textract_update_node_p_inv: forall V t0 t1 (ov: option V),
  (textract_node_p (tupdate_node_p t0 t1 ov)) = (t0, t1, ov).
Proof. intros. destruct t0, t1, ov; reflexivity. Qed.

Theorem tupdate_extract_node_p_inv: forall V t t0 t1 (ov: option V)
  (EXT: textract_node_p t = (t0, t1, ov)),
  (tupdate_node_p t0 t1 ov) = t.
Proof. intros. destruct t as [[| | |]|]; inversion EXT; subst; reflexivity. Qed.

Theorem tupdate_p_updated: forall V k t (v: V),
  tget_p (tupdate_p t k v) k = Some v.
Proof.
  induction k; intros; simpl; destruct (textract_node_p t) as [[t0 t1] ov];
  rewrite textract_update_node_p_inv; solve [apply IHk | reflexivity].
Qed.

Theorem tupdate_n_updated: forall V k t (v: V),
  tget_n (tupdate_n t k v) k = Some v.
Proof.
  intros. destruct t as [v0 tp]. unfold tget_n, tupdate_n.
  destruct k; try solve [reflexivity|apply tupdate_p_updated].
Qed.

Theorem tupdate_p_frame: forall V k k0 t (v: V) (NEQ: k0 <> k),
  tget_p (tupdate_p t k v) k0 = tget_p t k0.
Proof.
  induction k; intros; simpl; destruct textract_node_p as [[t0 t1] ov] eqn: EXT;
  (* if k0 != k by structure, very trivial *)
  destruct k0; simpl; rewrite textract_update_node_p_inv, EXT; trivial2.
  - (* ~1 *) apply IHk. intro Contra. subst. invalid NEQ.
  - (* ~0 *) apply IHk. intro Contra. subst. invalid NEQ.
  - (* H *) invalid NEQ.
Qed.

Theorem tupdate_n_frame: forall V k k0 t (v: V) (NEQ: k0 <> k),
  tget_n (tupdate_n t k v) k0 = tget_n t k0.
Proof.
  intros. destruct t. simpl.
  destruct k, k0; try solve [invalid NEQ | reflexivity].
  apply tupdate_p_frame. intro Contra. subst. invalid NEQ.
Qed.

Theorem tkeys_p_tkeys_extract: forall V (t t0 t1: treeP V) ov fn
  (EXT: textract_node_p t = (t0, t1, ov)),
  tkeys_p t fn = match ov with Some v => (fn xH :: nil) | None => nil end ++
    tkeys_p t0 (compose fn xO) ++ tkeys_p t1 (compose fn xI).
Proof.
  intros. destruct t as [[| | |]|]; inversion EXT; subst;
      repeat rewrite app_nil_r; reflexivity.
Qed.

Lemma tkeys_p_tupdate_node: forall V t0 t1 (ov: option V) fn,
  tkeys_p (tupdate_node_p t0 t1 ov) fn =
  match ov with
  | Some _ => fn 1%positive :: nil
  | None => nil
  end ++ tkeys_p t0 (compose fn xO) ++ tkeys_p t1 (compose fn xI).
Proof.
  intros. remember (tupdate_node_p _ _ _) as t. apply tkeys_p_tkeys_extract.
  subst. rewrite textract_update_node_p_inv. reflexivity.
Qed.

Theorem treeP_ind2: forall {V} (t: treeP V) (P: treeP V -> Prop)
  (BASE: P None) (IND: forall (t' tx0 tx1: treeP V) ov
    (IHt0: P tx0) (IHt1: P tx1) (EXT: textract_node_p t' = (tx0, tx1, ov)), P t'),
  P t.
Proof.
  destruct t as [t|]; [|intros; assumption]. induction t; intros.
  - (* leaf *) eapply IND; trivial2.
  - (* TP0 *) eapply IND; [|eassumption|reflexivity]. apply IHt; eassumption.
  - (* TP1 *) eapply IND; [eassumption| |reflexivity]. apply IHt; eassumption.
  - (* TP01 *) eapply IND; [| |reflexivity]. apply IHt1; eassumption.
    apply IHt2; eassumption.
Qed.

Theorem tkeys_p_fn_res: forall V (t: treeP V) p fn
  (InKeys: In p (tkeys_p t fn)), exists p0, p = fn p0.
Proof.
  intro. induction t as [|t tx0 tx1] using treeP_ind2; intros.
  - inversion InKeys.
  - erewrite tkeys_p_tkeys_extract in InKeys by eassumption.
    repeat rewrite in_app_iff in InKeys. destruct InKeys as [InOV|[InX0|InX1]].
    + destruct ov; inversion InOV; subst; try inversion H. eexists. reflexivity.
    + einversion trivial IHt1. eexists. reflexivity.
    + einversion trivial IHt2. eexists. reflexivity.
Qed.

Theorem tkeys_p_map: forall V (t: treeP V) fn,
  tkeys_p t fn = map fn (tkeys_p t ident).
Proof.
  intros until t. induction t as [|t tx0 tx1] using treeP_ind2; intros.
  - reflexivity.
  - repeat erewrite (tkeys_p_tkeys_extract _ t) by eassumption.
    repeat rewrite map_app. rewrite IHt1, IHt2. symmetry.
    rewrite IHt1, IHt2. repeat rewrite map_map. f_equal. destruct ov; reflexivity.
Qed.

Lemma tkeys_nexists_neq_h: forall V (val: option V) fn (p: positive)
    (INJ: injective fn) (NEQ: p <> 1%positive),
    (existsb (Pos.eqb (fn p))
        match val with
        | Some _ => fn 1 :: nil
        | None => nil
        end = false)%positive.
Proof.
  intros. destruct val; try reflexivity. simpl. rewrite orb_false_r.
  apply Pos.eqb_neq. apply injective_contra; trivial2.
Qed.

Lemma tkeys_nexists_neq_0: forall V fn (p: positive) (t: treeP V)
    (INJ: injective fn) (NEQ: forall p0, (p0~0)%positive <> p),
    (existsb (Pos.eqb (fn p))
      (tkeys_p t (fun p0 : positive => fn (p0~0)%positive)) = false)%positive.
Proof.
  intros. apply not_true_is_false. intro Contra.
  apply existsb_exists, Exists_exists in Contra. revert Contra.
  apply Forall_Exists_neg, Forall_forall. intros p0 InKeys Contra.
  einversion trivial tkeys_p_fn_res as [p']. apply Pos.eqb_eq in Contra.
  apply INJ in Contra. subst. specialize (NEQ p'). invalid NEQ.
Qed.

Lemma tkeys_nexists_neq_1: forall V fn (p: positive) (t: treeP V)
    (INJ: injective fn) (NEQ: forall p0, (p0~1)%positive <> p),
    (existsb (Pos.eqb (fn p))
      (tkeys_p t (fun p0 : positive => fn (p0~1)%positive)) = false)%positive.
Proof.
  intros. apply not_true_is_false. intro Contra.
  apply existsb_exists, Exists_exists in Contra. revert Contra.
  apply Forall_Exists_neg, Forall_forall. intros p0 InKeys Contra.
  einversion trivial tkeys_p_fn_res as [p']. apply Pos.eqb_eq in Contra.
  apply INJ in Contra. subst. specialize (NEQ p'). invalid NEQ.
Qed.

Theorem tkeys_p_get: forall V p fn (t: treeP V)
  (INJ: injective fn),
  existsb (Pos.eqb (fn p)) (tkeys_p t fn) = tcontains_p t p.
Proof.
  unfold tcontains_p. induction p; intros; simpl;
  destruct textract_node_p as [[t0 t1] ov] eqn: EXT;
  erewrite tkeys_p_tkeys_extract by eassumption.
  - (* ~1 *) rewrite existsb_app, existsb_app, tkeys_nexists_neq_h,
    tkeys_nexists_neq_0 by trivial2. simpl.
    apply (IHp (fun p => fn (xI p))). prove_injective.
  - (* ~0 *) rewrite existsb_app, existsb_app, tkeys_nexists_neq_h,
      tkeys_nexists_neq_1 by trivial2. simpl.
    rewrite orb_false_r. apply (IHp (fun p => fn (xO p))). prove_injective.
  - (* H *) rewrite existsb_app, existsb_app, tkeys_nexists_neq_0,
      tkeys_nexists_neq_1 by trivial2. simpl.
    rewrite orb_false_r. destruct ov; simpl. rewrite Pos.eqb_refl.
    reflexivity. reflexivity.
Qed.

Theorem tkeys_n_get: forall V n (t: treeN V),
  existsb (N.eqb n) (tkeys_n t) = tcontains_n t n.
Proof.
  unfold tcontains_n, tget_n. intros. destruct t, n; simpl.
  - (* 0 *) rewrite existsb_app.
    eassert (EXB2: existsb _ (map _ _) = false); [|rewrite EXB2].
      apply not_true_is_false. intro Contra.
      apply existsb_exists, Exists_exists in Contra. revert Contra.
      apply Forall_Exists_neg, Forall_forall. intros n0 InKeys Contra.
      apply N.eqb_eq in Contra. subst. apply in_map_iff in InKeys.
      destruct InKeys as [x [Contra _]]. discriminate.
    rewrite orb_false_r. destruct v0; reflexivity.
  - (* Pos *) rewrite existsb_app. eassert (EXB1: existsb _ _ = false);
      [|rewrite EXB1]. destruct v0; reflexivity.
    simpl. fold (tcontains_p tp p). assert (injective (@ident positive)).
    prove_injective.
    destruct tcontains_p eqn: TC;
      erewrite <- tkeys_p_get with (fn := ident) in TC by assumption.
    + (* true *) apply existsb_exists in TC. apply existsb_exists. unfold ident in *.
      destruct TC as [p' [InKeys Eq]]. apply Pos.eqb_eq in Eq. subst. eexists.
      rewrite N.eqb_eq. split; [|reflexivity]. apply in_map_iff.
      eexists. split. reflexivity. assumption.
    + (* false *) apply not_true_is_false. apply not_true_iff_false in TC.
      intro Contra. apply TC. clear TC. apply existsb_exists in Contra.
      apply existsb_exists. unfold ident in *. destruct Contra as [p' [InKeys Eq]].
      apply N.eqb_eq in Eq. subst. eexists. rewrite Pos.eqb_eq.
      split; [|reflexivity]. apply in_map_iff in InKeys.
      destruct InKeys as [p' [EQ In]]. inversion EQ. subst. assumption.
Qed.

Corollary tkeys_p_in_contains: forall V k (t: treeP V),
  tcontains_p t k = true <-> In k (tkeys_p t ident).
Proof.
  intros. rewrite <- (tkeys_p_get _ _ ident). unfold ident. split; intros.
  - apply existsb_exists in H. destruct H as [x [InKeys EQ]].
    apply Pos.eqb_eq in EQ. subst. assumption.
  - apply existsb_exists. eexists. split. eassumption. apply Pos.eqb_refl.
  - prove_injective.
Qed.

Corollary tkeys_p_in_contains_contra: forall V k (t: treeP V),
  tcontains_p t k = false <-> ~(In k (tkeys_p t ident)).
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive tkeys_p_in_contains.
Qed.

Corollary tkeys_n_in_contains: forall V k (t: treeN V),
  tcontains_n t k = true <-> In k (tkeys_n t).
Proof.
  intros. rewrite <- tkeys_n_get, Neqb_iseqb_fn. apply existsb_iseqb_iff_in.
Qed.

Corollary tkeys_n_in_contains_contra: forall V k (t: treeN V),
  tcontains_n t k = false <-> ~(In k (tkeys_n t)).
Proof.
  intros. rewrite <- not_true_iff_false. contrapositive tkeys_n_in_contains.
Qed.

Theorem tkeys_p_nodup: forall V (t: treeP V) fn (INJ: injective fn),
  NoDup (tkeys_p t fn).
Proof.
  intros until t. induction t as [|t tx0 tx1] using treeP_ind2; intros.
  - constructor.
  - repeat erewrite (tkeys_p_tkeys_extract _ t) by eassumption.
    rewrite tkeys_p_map, (tkeys_p_map _ tx1). unfold compose.
    (* Prove no duplicates when we merge t1 and t2 *)
    eassert (NoDup _); [|destruct ov; simpl; [constructor|]; try eassumption].
    apply NoDup_app. apply NoDup_map_inj. prove_injective. apply IHt1. prove_injective.
    apply NoDup_map_inj. prove_injective. apply IHt2. prove_injective. intros.
    apply in_map_iff in InL, InL'. destruct InL as [a' [EQa INt1]].
    destruct InL' as [b' [EQb INt2]]. subst. intros Contra. apply INJ in Contra.
    inversion Contra.

    (* Prove 1 is not in the merged t1/t2 *)
    intros Contra. apply in_app_or in Contra. destruct Contra as [C|C];
    apply in_map_iff in C; destruct C as [a [EQa INt]];
    apply INJ in EQa; inversion EQa.
Qed.

Theorem tkeys_n_nodup: forall V (t: treeN V), NoDup (tkeys_n t).
Proof.
  intros. unfold tkeys_n. destruct t.
  assert (NoDup (map N.pos (tkeys_p tp ident))).
    apply NoDup_map_inj; try apply tkeys_p_nodup; prove_injective.
  destruct v0; [|assumption]. constructor; [|assumption]. intros Contra.
  apply in_map_iff in Contra. destruct Contra as [a [EQa INt2]]. discriminate.
Qed.

Theorem tupdate_p_idempotent: forall V k (v: V) t (LU: tget_p t k = Some v),
  (tupdate_p t k v) = t.
Proof.
  induction k; intros; simpl in *; destruct textract_node_p as [[tx0 tx1] ov] eqn: EXT.
  - (* ~1 *) rewrite IHk; try apply tupdate_extract_node_p_inv; assumption.
  - (* ~0 *) rewrite IHk; try apply tupdate_extract_node_p_inv; assumption.
  - (* H *) subst. apply tupdate_extract_node_p_inv. assumption.
Qed.

Theorem tupdate_n_idempotent: forall V k (v: V) t (LU: tget_n t k = Some v),
  (tupdate_n t k v) = t.
Proof.
  unfold tupdate_n. intros. destruct t, k; simpl in *.
  - (* 0 *) subst. reflexivity.
  - (* Pos *) rewrite tupdate_p_idempotent; trivial2.
Qed.

Lemma tree_p_disjoint_H_x01: forall V (val: option V) fn (t1 t2: treeP V) a b
  (INJ: injective fn)
  (In1: In a match val with
             | Some _ => fn 1%positive :: nil
             | None => nil
             end)
  (In2: In b
    (tkeys_p t1 (fun p => fn (p~0)%positive) ++
     tkeys_p t2 (fun p => fn (p~1)%positive))), a <> b.
Proof.
  intros. destruct val; inversion In1; inversion H. subst. clear H0.
  apply in_app_or in In2. intro Contra. subst. rewrite tkeys_p_map,
    (tkeys_p_map _ t2), in_map_iff, in_map_iff in In2.
  destruct In2 as [[p [Contra _]]|[p [Contra _]]];
  apply INJ in Contra; inversion Contra.
Qed.

Lemma tree_p_disjoint_x0_x1: forall V (val: option V) fn (t1 t2: treeP V) a b
  (INJ: injective fn)
  (In1: In a (tkeys_p t1 (fun p => fn (p~0)%positive)))
  (In2: In b (tkeys_p t2 (fun p => fn (p~1)%positive))), a <> b.
Proof.
  intros. rewrite tkeys_p_map, in_map_iff in *.
  destruct In1 as [a' [EQA _]]. destruct In2 as [b' [EQB _]]. subst.
  apply injective_contra. assumption. discriminate.
Qed.

Theorem tkeys_p_equiv_equal: forall V (t1 t2: treeP V) fn (INJ: injective fn)
  (EQV: list_equiv (tkeys_p t1 fn) (tkeys_p t2 fn)),
    tkeys_p t1 fn = tkeys_p t2 fn.
Proof.
  intros until t1. induction t1 as [|t1 t1_x0 t1_x1 ov1] using treeP_ind2; intros.
  - (* base *) simpl in EQV. destruct EQV as [_ Nil]. apply incl_l_nil in Nil.
    rewrite Nil. reflexivity.
  - (* induct *) destruct (textract_node_p t2) as [[t2_x0 t2_x1] ov2] eqn: EXT2.
    repeat erewrite (tkeys_p_tkeys_extract _ t1) in * by eassumption.
    repeat erewrite (tkeys_p_tkeys_extract _ t2) in * by eassumption.
    apply (list_equiv_partition positive) in EQV;
      try (intros; eapply tree_p_disjoint_H_x01; eassumption).
    destruct EQV as [EQV_H EQV_x01].
    apply (list_equiv_partition positive) in EQV_x01;
      try (intros; eapply tree_p_disjoint_x0_x1; eassumption).
    unfold compose in *. destruct EQV_x01 as [EQV_x0 EQV_x1]. f_equal; [|f_equal].
    + destruct ov1, ov2; solve [ reflexivity
      | destruct (list_nequiv_1 _ _ _ EQV_H)
      | destruct (list_nequiv_2 _ _ _ EQV_H) ].
    + apply IHt1_1. prove_injective. assumption.
    + apply IHt1_2. prove_injective. assumption.
Qed.

Lemma tree_n_disjoint_0_pos: forall V (ov0: option V) (tp: treeP V) a b
  (In1: In a match ov0 with
       | Some _ => 0 :: nil
       | None => nil
       end)
  (In2: In b (map N.pos (tkeys_p tp ident))), a <> b.
Proof.
  intros. destruct ov0; inversion In1; subst; try inversion H. intro EQ. subst.
  apply in_map_iff in In2. destruct In2 as [n' [Contra _]]. discriminate.
Qed.

Theorem tkeys_n_equiv_equal: forall V (t1 t2: treeN V)
  (EQV: list_equiv (tkeys_n t1) (tkeys_n t2)),
    tkeys_n t1 = tkeys_n t2.
Proof.
  intros. destruct t1 as [t1_ov0 t1]. destruct t2 as [t2_ov0 t2].
  simpl in *. apply (list_equiv_partition N) in EQV;
    try (intros; eapply tree_n_disjoint_0_pos; eassumption).
  destruct EQV as [EQV0 EQV_P]. f_equal.
  - (* 0 *) destruct t1_ov0, t2_ov0; solve [ reflexivity
    | destruct (list_nequiv_1 _ _ _ EQV0)
    | destruct (list_nequiv_2 _ _ _ EQV0) ].
  - (* Pos *) f_equal. apply tkeys_p_equiv_equal. prove_injective.
    rewrite <- list_equiv_map_iff in EQV_P by prove_injective. assumption.
Qed.

Lemma is_empty_forallb: forall A (l: list A),
  is_empty l = forallb (fun _ => false) l.
Proof. intros. destruct l; reflexivity. Qed.

Lemma is_empty_length: forall A (l: list A),
  is_empty l = (length l =? 0)%nat.
Proof. intros. destruct l; reflexivity. Qed.

Theorem tempty_p_keys_empty: forall V (t: treeP V) fn,
  tempty_p t = is_empty (tkeys_p t fn).
Proof.
  intros. rewrite is_empty_forallb. revert_all. intros until t.
  induction t as [|t t_x0 t_x1 ov] using treeP_ind2; intros.
  - reflexivity.
  - repeat erewrite (tkeys_p_tkeys_extract _ t) in * by eassumption.
    repeat rewrite forallb_app. rewrite <- IHt1, <- IHt2.
    destruct t as [[| | |]|]; inversion EXT; subst; try rewrite andb_false_r;
    reflexivity.
Qed.

Lemma tupdate_p_nonempty: forall V (v: V) k t fn,
  is_empty (tkeys_p (t [Ⓟ  k := v]) fn) = false.
Proof.
  intros. rewrite is_empty_forallb. revert_all. induction k; intros; simpl in *;
  destruct (textract_node_p t) as [[tx0 tx1] ov] eqn: EXT;
  repeat erewrite tkeys_p_tupdate_node; repeat rewrite forallb_app.
  - (* ~1 *) rewrite IHk. repeat rewrite andb_false_r. reflexivity.
  - (* ~0 *) rewrite IHk. repeat rewrite andb_false_r. reflexivity.
  - (* H *) reflexivity.
Qed.

Theorem tempty_n_keys_empty: forall V (t: treeN V),
  tempty_n t = is_empty (tkeys_n t).
Proof.
  intros. destruct t, v0. reflexivity. simpl. rewrite is_empty_length,
  map_length, <- is_empty_length. apply tempty_p_keys_empty.
Qed.

Lemma tupdate_n_nonempty: forall V (v: V) k t,
  is_empty (tkeys_n (t [Ⓝ  k := v])) = false.
Proof.
  intros. rewrite <- tempty_n_keys_empty. destruct t, k. reflexivity. simpl.
  destruct v0; try reflexivity. erewrite tempty_p_keys_empty with (fn:=ident).
  apply tupdate_p_nonempty.
Qed.

Theorem tkeys_p_inj: forall V (t1 t2: treeP V) fn
  (VALS:forall v, tcontains_p t1 v = tcontains_p t2 v -> tget_p t1 v = tget_p t2 v)
  (KEQ: tkeys_p t1 fn = tkeys_p t2 fn) (INJ: injective fn), t1 = t2.
Proof.
  intros until t1. induction t1 as [|t1 t1_x0 t1_x1 ov1] using treeP_ind2; intros.
  - einstantiate (tempty_p_keys_empty V None) as Nil.
    rewrite KEQ, <- tempty_p_keys_empty in Nil. destruct t2. discriminate.
    reflexivity.
  - erewrite (tkeys_p_tkeys_extract _ t1) in * by eassumption.
    destruct (textract_node_p t2) as [[t2_x0 t2_x1] ov2] eqn: EXT2.
    erewrite (tkeys_p_tkeys_extract _ t2) in * by eassumption.

    (* Partition KEQ *)
    apply list_app_partition in KEQ;
      try (intros; eapply tree_p_disjoint_H_x01; eassumption).
    destruct KEQ as [KEQ_H KEQ_x01].
    apply list_app_partition in KEQ_x01;
      try (intros; eapply tree_p_disjoint_x0_x1; eassumption).
    destruct KEQ_x01 as [KEQ_x0 KEQ_x1].

    (* ov1 = ov2 because of VALS and KEQ_H *)
    assert (ov1 = ov2). destruct ov1, ov2; trivial2.
      unfold tcontains_p in *. einstantiate (VALS xH) as VALS. simpl.
      rewrite EXT, EXT2. reflexivity. simpl in VALS. rewrite EXT, EXT2 in VALS.
      assumption. subst.

    (* Now apply IH's *)
    einstantiate trivial (IHt1_1 t2_x0). intros.
      einstantiate (VALS (xO v)). unfold tcontains_p. simpl. rewrite EXT, EXT2.
      assumption. simpl in H0. rewrite EXT, EXT2 in H0. assumption.
      unfold compose. prove_injective.
    einstantiate trivial (IHt1_2 t2_x1). intros.
      einstantiate (VALS (xI v)). unfold tcontains_p. simpl. rewrite EXT, EXT2.
      assumption. simpl in H1. rewrite EXT, EXT2 in H1. assumption.
      unfold compose. prove_injective.

    (* Parts are equal, so whole part is equal too *)
    subst. erewrite <- (tupdate_extract_node_p_inv _ t1),
      <- (tupdate_extract_node_p_inv _ t2) by eassumption. reflexivity.
Qed.

Theorem tkeys_n_inj: forall V (t1 t2: treeN V)
  (VALS:forall v, tcontains_n t1 v = tcontains_n t2 v -> tget_n t1 v = tget_n t2 v)
  (KEQ: tkeys_n t1 = tkeys_n t2), t1 = t2.
Proof.
  intros. destruct t1 as [t1_v0 t1]. destruct t2 as [t2_v0 t2]. simpl in KEQ.
  apply list_app_partition in KEQ;
    try (intros; eapply tree_n_disjoint_0_pos; eassumption).
  destruct KEQ as [KEQ1 KEQ2]. f_equal.
  - destruct t1_v0, t2_v0; trivial2. specialize (VALS 0). simpl in VALS.
    apply VALS. reflexivity.
  - eapply tkeys_p_inj.
    (* VALS *) intros. specialize (VALS (Npos v)). apply VALS. assumption.
    (* KEQ *) eapply map_inj; trivial2. prove_injective.
    (* INJ *) prove_injective.
Qed.

(* Set library *)
Definition set := treeN unit.
Declare Scope sets_scope.
Bind Scope sets_scope with set.

Definition set_nil: set := treeN_nil.
Definition set_elems: set -> list N := tkeys_n.
Definition set_has: set -> N -> bool := tcontains_n.
Definition set_empty: set -> bool := tempty_n.

Definition set_add a (s: set): set := s [Ⓝ  a := tt ].
Arguments set_add: simpl never.
Notation "h ~:: t" := (set_add h t) (at level 60, right associativity):
  sets_scope.

Fixpoint set_add_all (s1: set) (l2: list N): set :=
  match l2 with
  | nil => s1
  | h::t => set_add h (set_add_all s1 t)
  end.

Definition list_to_set (l: list N): set := set_add_all set_nil l.

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

Theorem set_add_nonempty: forall (s: set) a,
  set_empty (a ~:: s) = false.
Proof.
  intros. unfold set_empty, set_add. rewrite tempty_n_keys_empty.
  apply tupdate_n_nonempty.
Qed.

Theorem set_empty_nil: forall (s: set), s = set_nil <-> set_empty s = true.
Proof.
  split. intro Nil. subst. reflexivity. intro Empty. destruct s.
  destruct v0; try discriminate. destruct tp; trivial2.
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
  (NEQ: a1 <> a2) (InAdd: In a1 (set_elems (a2 ~:: s))), In a1 (set_elems s).
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

