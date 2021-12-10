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

Program Instance bool_EqDec : EqDec bool.
Next Obligation. Proof. decide equality. Defined.

Program Instance option_EqDec A `(EA : EqDec A) : EqDec (option A).
Next Obligation. Proof. decide equality. apply iseq. Defined.

Program Instance tuple_EqDec A B `(EA : EqDec A) `(EA : EqDec B): EqDec (A * B).
Next Obligation. Proof. decide equality; apply iseq. Defined.

Program Instance list_EqDec A `(EA : EqDec A) : EqDec (list A).
Next Obligation. Proof. decide equality. apply iseq. Defined.

(* We define a store delta as a variable to partial mapping onto
 * some expression. This is partial to account for "undefined" variables (which
 * could also be undefined "memory" variables) *)
Definition store_delta := list (var * option exp).

(* Convert a list of variables and their values to a store function. *)
Fixpoint delta_updlst s (l: store_delta) : var ⇀ exp :=
  match l with nil => s | (v,e)::t => update (delta_updlst s t) v e end.

(* Remove a variable from a list of variables and their values. *)
Fixpoint remlst v (l: store_delta) : store_delta :=
  match l with
  | nil => nil
  | (v',u)::t => if v == v' then remlst v t else (v',u)::(remlst v t)
  end.

Definition setlst (l: store_delta) v e: store_delta := (v, e) :: remlst v l.
Notation "f [[ x := y ]]" := (setlst f x y) (at level 50, left associativity).

Definition vdomain := var -> bool.
Definition init_delta (domain: vdomain): var ⇀ exp := fun v =>
  if domain v then Some (Var v) else None.
Notation "f <{ domain }> [[ x ]]" :=
  (delta_updlst (init_delta domain) f x)
  (at level 50, left associativity).

Definition trim_delta_state (vd: vdomain) (δ: store_delta) :=
  flat_map (fun '(v, e) => if vd v then (v, e) :: nil else nil) δ.

Definition has_delta (vd: vdomain) (h: hdomain) (s0 s: store) (δ: store_delta) :=
  forall v e val (LUv: δ<{vd}>[[v]] = Some e) (EE: eval_exp h s0 e val), s v = val.

Definition delta_nounk (vd: vdomain) (δ: store_delta) :=
  forall v e (LUv: δ<{vd}>[[v]] = Some e), forall_exps_in_exp not_unknown e.

Definition delta_defined (δ: store_delta) :=
  map fst δ.

Definition delta_equivb (vd: vdomain) (δ1 δ2: store_delta) :=
  forallb (fun '(v, _) => iseqb (δ1<{vd}>[[v]]) (δ2<{vd}>[[v]])) (δ1 ++ δ2).

Definition delta_equiv (vd: vdomain) (δ1 δ2: store_delta) :=
  forall v, δ1<{vd}>[[v]] = δ2<{vd}>[[v]].

Definition delta_same_domain (vd: vdomain) (δ1 δ2: store_delta) :=
  forall v, match (δ1<{vd}>[[v]]), (δ2<{vd}>[[v]]) with
            | Some _, Some _ => True
            | None, None => True
            | _, _ => False
            end.

Theorem delta_updlst_def: forall f δ v (ND: ~(In v (delta_defined δ))),
  delta_updlst f δ v = f v.
Proof.
  induction δ; intros.
  - reflexivity.
  - simpl. destruct a as [v' e']. rewrite update_frame. apply IHδ.
    intros Contra. apply ND. right. assumption.
    intro. subst. apply ND. left. reflexivity.
Qed.

Lemma neq_sym: forall A (n m: A), n <> m -> m <> n.
Proof.
  intros. intro. subst. apply H. reflexivity.
Qed.

Theorem delta_remlst_removed: forall δ fn v,
  delta_updlst fn (remlst v δ) v = fn v.
Proof.
  intros. apply delta_updlst_def. intros Contra. revert v Contra. induction δ; intros. 
  - inversion Contra.
  - simpl in Contra. destruct a as [v' u']. eapply IHδ. destruct (v == v').
    eassumption. apply neq_sym in n. destruct Contra; [contradiction n|assumption].
Qed.

Theorem delta_remlst_frame: forall δ fn x z (NEQ: z ≠ x),
  delta_updlst fn (remlst x δ) z = delta_updlst fn δ z.
Proof.
  induction δ; intros.
  - reflexivity.
  - simpl. destruct a as [v' e']. destruct (z == v').
    + subst. apply neq_sym in NEQ. vantisym x v' by assumption. simpl.
      repeat rewrite update_updated. reflexivity.
    + simpl. rewrite update_frame by assumption. destruct (x == v').
      apply IHδ. assumption. simpl. rewrite update_frame by assumption.
      apply IHδ. assumption.
Qed.

Theorem delta_update_updated: forall fn δ x y, delta_updlst fn (δ [[x := y]]) x = y.
Proof. intros. unfold setlst. simpl. apply update_updated. Qed.

Theorem delta_update_frame: forall δ fn x y z (NEQ: z ≠ x),
  delta_updlst fn (δ [[x := y]]) z = delta_updlst fn δ z.
Proof.
  intros. unfold setlst. simpl. rewrite update_frame by assumption.
  apply delta_remlst_frame. assumption.
Qed.

Theorem delta_delta_updlst_iff_defined: forall f δ v,
  In v (delta_defined δ) <-> In (v, delta_updlst f δ v) δ.
Proof.
  split.
  - intro InDef. revert_all. induction δ; intros.
    + inversion InDef.
    + simpl in *. destruct a as [v' e']. destruct (v == v').
      * subst. left. rewrite update_updated. reflexivity.
      * destruct InDef. subst. contradiction n. reflexivity. right.
        rewrite update_frame by assumption. apply IHδ; assumption.
  - intro InDelta. revert_all. induction δ; intros.
    + inversion InDelta.
    + destruct a as [v' e']. destruct (v == v'); subst; simpl in *.
      * left. reflexivity.
      * destruct InDelta. inversion H. subst. contradict n. reflexivity.
        right. apply IHδ. rewrite update_frame in H; assumption.
Qed.

Corollary delta_delta_updlst_iff_defined_contra: forall f δ v,
  ~ In v (delta_defined δ) <-> ~ In (v, delta_updlst f δ v) δ.
Proof. intros. contrapositive delta_delta_updlst_iff_defined. Qed.

Theorem delta_equivb_iff_delta_equiv: forall vd δ1 δ2,
  delta_equivb vd δ1 δ2 = true <-> delta_equiv vd δ1 δ2.
Proof.
  unfold delta_equiv, delta_equivb. split; intro EQV.
  - (* -> *) intro. rewrite forallb_app, andb_true_iff in EQV.
    destruct EQV as [EQV1 EQV2]. edestruct (in_dec iseq (v, δ1<{vd}>[[v]])).
    + eapply forallb_forall in EQV1; [|eassumption]. simpl in EQV1.
      unfold iseqb in EQV1. destruct (_ == _); try discriminate. assumption.
    + edestruct (in_dec iseq (v, δ2<{vd}>[[v]])).
      * eapply forallb_forall in EQV2; [|eassumption]. simpl in EQV2.
        unfold iseqb in EQV2. destruct (_ == _); try discriminate. assumption.
      * repeat rewrite delta_updlst_def; try rewrite delta_delta_updlst_iff_defined_contra;
        trivial2.
  - (* <- *) rewrite forallb_forall. intros. destruct x as [v e]. rewrite EQV.
    unfold iseqb. vreflexivity (δ2<{vd}>[[v]]). reflexivity.
Qed.

Corollary delta_equivb_iff_delta_equiv_contra: forall vd δ1 δ2,
  delta_equivb vd δ1 δ2 = false <-> ~ delta_equiv vd δ1 δ2.
Proof.
  intros. rewrite <- not_true_iff_false.
  contrapositive delta_equivb_iff_delta_equiv.
Qed.

Lemma trim_delta_state_preserve: forall vd δ v
  (VD: vd v = true), trim_delta_state vd δ <{vd}>[[v]] = δ<{vd}>[[v]].
Proof.
  induction δ; intros.
  - reflexivity.
  - destruct a as [v' e']. simpl. destruct (v == v').
    + subst. rewrite VD. simpl. repeat rewrite update_updated.
      reflexivity.
    + einstantiate trivial IHδ. destruct (vd v'); simpl;
      repeat rewrite update_frame; assumption.
Qed.

Theorem trim_delta_state_correct: forall vd δ h s0 s
  (HD: has_delta vd h s0 s δ), has_delta vd h s0 s (trim_delta_state vd δ).
Proof.
  unfold has_delta. intros. destruct (vd v) eqn: VD.
  - rewrite trim_delta_state_preserve in LUv by assumption.
    eapply HD; eassumption.
  - unfold trim_delta_state, init_delta in LUv. rewrite delta_updlst_def, VD in LUv.
    discriminate. intro InMap. unfold delta_defined in InMap.
    rewrite flat_map_concat_map, concat_map, map_map,
      <- flat_map_concat_map, in_flat_map in InMap.
    destruct InMap as [ [v' e'] [InDelta InVD] ].
    destruct (vd v') eqn: VD'; inversion InVD; subst; try inversion H.
    simpl in *. rewrite VD in VD'. discriminate.
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

Lemma has_delta_assign_None: forall vd h s s' δ v u (HD: has_delta vd h s s' δ),
  has_delta vd h s (s' [v := u]) (δ [[v := None]]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite delta_update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    rewrite update_frame by assumption. eapply HD; eassumption.
Qed.

Lemma has_delta_assign_Some: forall vd h s s' δ v e u (HD: has_delta vd h s s' δ)
  (EQ: forall u' (EE: eval_exp h s e u'), u = u'),
  has_delta vd h s (s' [v := u]) (δ [[v := Some e]]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite delta_update_updated in LUv.
    inversion LUv; subst. apply EQ. assumption.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    rewrite update_frame by assumption. eapply HD; eassumption.
Qed.

Lemma delta_nounk_assign_None: forall vd v δ (DNU: delta_nounk vd δ),
  delta_nounk vd (δ [[v := None]]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite delta_update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Lemma delta_nounk_assign_Some: forall vd v δ e (DNU: delta_nounk vd δ)
  (NUnk: forall_exps_in_exp not_unknown e),
  delta_nounk vd (δ [[v := Some e]]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite delta_update_updated in LUv. inversion LUv; subst. assumption.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Theorem delta_same_domain_refl: forall vd δ, delta_same_domain vd δ δ.
Proof.
  unfold delta_same_domain. intros.
  destruct (δ<{vd}>[[v]]); reflexivity.
Qed.

Theorem delta_same_domain_assign: forall vd v δ1 δ2 o1 o2
  (Sim: match o1, o2 with
        | Some _, Some _ => True
        | None, None => True
        | _, _ => False
        end)
  (DSD: delta_same_domain vd δ1 δ2),
  delta_same_domain vd (δ1[[v := o1]]) (δ2[[v := o2]]).
Proof.
  unfold delta_same_domain. intros. destruct (v == v0).
  - subst. repeat rewrite delta_update_updated. destruct o1, o2;
    solve [reflexivity|contradiction Sim].
  - apply neq_sym in n. repeat rewrite delta_update_frame by assumption. apply DSD.
Qed.

Fixpoint subst_valid (vd: vdomain) (δ: store_delta) e: bool :=
  match e with
  | Var v =>
      match δ<{vd}>[[v]] with
      | Some e => true
      | None => false
      end
  | Word _ _ => true
  | Load e1 e2 _ _ => subst_valid vd δ e1 && subst_valid vd δ e2
  | Store e1 e2 e3 _ _ => subst_valid vd δ e1 && subst_valid vd δ e2 && subst_valid vd δ e3
  | BinOp _ e1 e2 => subst_valid vd δ e1 && subst_valid vd δ e2
  | UnOp _ e => subst_valid vd δ e
  | Cast _ _ e => subst_valid vd δ e
  | Let v e e_in =>
      if subst_valid vd δ e
      then subst_valid vd (δ[[v := (Some (Word 0 0))]]) e_in
      else subst_valid vd (δ[[v := None]]) e_in
  | Unknown _ => false
  | Ite e1 e2 e3 => subst_valid vd δ e1 && subst_valid vd δ e2 && subst_valid vd δ e3
  | Extract _ _ e => subst_valid vd δ e
  | Concat e1 e2 => subst_valid vd δ e1 && subst_valid vd δ e2
  end.

Fixpoint subst_exp0 (vd: vdomain) (δ: store_delta) e: exp :=
  match e with
  | Var v =>
      match δ<{vd}>[[v]] with
      | Some e => e
      | None => Unknown 0 (* Note we should return error in subst_err here *)
      end
  | Word _ _ => e
  | Load e1 e2 en len => Load (subst_exp0 vd δ e1) (subst_exp0 vd δ e2) en len
  | Store e1 e2 e3 en len => Store (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
      (subst_exp0 vd δ e3) en len
  | BinOp op e1 e2 => BinOp op (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
  | UnOp op e => UnOp op (subst_exp0 vd δ e)
  | Cast typ w' e => Cast typ w' (subst_exp0 vd δ e)
  | Let v e e_in =>
      if subst_valid vd δ e
      then subst_exp0 vd (δ[[v := (Some (subst_exp0 vd δ e))]]) e_in
      else subst_exp0 vd (δ[[v := None]]) e_in
  | Unknown _ => e
  | Ite e1 e2 e3 => Ite (subst_exp0 vd δ e1) (subst_exp0 vd δ e2) (subst_exp0 vd δ e3)
  | Extract n1 n2 e => Extract n1 n2 (subst_exp0 vd δ e)
  | Concat e1 e2 => Concat (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
  end.

Definition subst_exp (vd: vdomain) (δ: store_delta) e: option exp :=
  if subst_valid vd δ e then Some (subst_exp0 vd δ e) else None.

Theorem subst_valid_any_Some: forall vd e δ1 δ2
  (DSD: delta_same_domain vd δ1 δ2),
  subst_valid vd δ1 e = subst_valid vd δ2 e.
Proof.
  induction e; intros; simpl; try erewrite IHe1 by eassumption;
  try erewrite IHe2 by eassumption; try erewrite IHe3 by eassumption;
  try erewrite IHe by eassumption; try reflexivity.

  (* Var *) specialize (DSD v). destruct (δ1<{vd}>[[v]]), (δ2<{vd}>[[v]]);
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
             | IH: forall (DNU: delta_nounk _ δ), _ |- _ =>
                 einstantiate trivial IH as IH
             end
  end.

Theorem subst_exp0_nounk: forall vd e δ (DNU: delta_nounk vd δ)
  (SE: subst_valid vd δ e = true),
  forall_exps_in_exp not_unknown (subst_exp0 vd δ e).
Proof.
  unfold subst_exp; induction e; intros; simpl in SE;
  try solve [exp_destruction_nounk; repeat split; assumption + reflexivity].
  - (* Var *) destruct (δ<{vd}>[[v]]) eqn: LUv; inversion SE. subst. eapply DNU.
    simpl. rewrite LUv. reflexivity.
  - (* Let *) simpl. destruct subst_valid eqn: SV1.
    + (* e1 is valid *) apply IHe2. apply delta_nounk_assign_Some. assumption.
      apply IHe1; assumption. erewrite subst_valid_any_Some. eassumption.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) apply IHe2. apply delta_nounk_assign_None.
      assumption. assumption.
Qed.

Theorem subst_exp_nounk: forall vd e e' δ (DNU: delta_nounk vd δ)
  (SE: subst_exp vd δ e = Some e'), forall_exps_in_exp not_unknown e'.
Proof.
  unfold subst_exp. intros. destruct subst_valid eqn: SV; inversion SE.
  subst. apply subst_exp0_nounk; assumption.
Qed.

Local Ltac exp_destruction_correct :=
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

Theorem subst_exp_correct: forall vd s0 h e e' s δ v v'
  (HD: has_delta vd h s0 s δ) (SE: subst_exp vd δ e = Some e') (EE: eval_exp h s e v)
  (EE': eval_exp h s0 e' v'), v = v'.
Proof.

  intros. move δ before e. repeat lazymatch goal with H:_ |- _ => revert H end.

  unfold subst_exp; induction e; intros; inversion EE; subst;
  simpl in SE; clear EE; try solve [exp_destruction_correct; reflexivity].
  - (* Var *) destruct (δ<{vd}>[[v]]) eqn: LUv; inversion SE. subst. erewrite HD;
    solve [reflexivity|eassumption].
  - (* Let *) destruct subst_valid eqn: SV1.
    + (* e1 is valid *) erewrite subst_valid_any_Some in SE. eapply IHe2;
      [| eassumption | eassumption | eassumption]. apply has_delta_assign_Some.
      assumption. intros. destruct (subst_valid _ _ e2) eqn: SV2; inversion SE.
      eapply IHe1; try eassumption. rewrite SV1. reflexivity.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) eapply IHe2; [| eassumption | eassumption | eassumption].
      apply has_delta_assign_None. assumption.
  - (* Ite *) exp_destruction_correct. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe2 as IHe2.
Qed.

Definition trace_states := treeN store_delta.

Inductive jump_target: Set :=
  | jump_addr (a: addr)
  | jump_symbolic. (* a call or return *)


Inductive eval_jump (p: program) (s: store):
  addr -> jump_target -> Prop :=
  | EJ_jump_addr (a: addr): eval_jump p s a (jump_addr a)
  | EJ_jump_symbolic (a: addr) (LU: p s a = None):
      eval_jump p s a jump_symbolic.

Definition eval_jump_targets p s a (jmps: list jump_target): Prop :=
  Exists (eval_jump p s a) jmps.

Inductive ts_evidence :=
  | has_jump_targets (a1: addr) (q0: stmt) (δ: store_delta) (vd: vdomain)
      (e: exp) (jmps: list jump_target).

Inductive ts_evidence_proved (p: program) (h: hdomain)
  (a0: addr) (s0: store): ts_evidence -> Prop :=
  | EV_has_jump_targets (a1: addr) (q0: stmt) (δ: store_delta)
      (vd: vdomain) (e: exp) (jmps: list jump_target) (EJT: forall n a' s0' s1
        (XP: exec_prog h p a0 s0 n s0' (Exit a1))
        (XS0: exec_stmt h s0' q0 s1 None)
        (XS: exec_stmt h s1 (Jmp e) s1 (Some (Exit a')))
        (HD: has_delta vd h s0 s1 δ),
        eval_jump_targets p s1 a' jmps):
        ts_evidence_proved p h a0 s0 (has_jump_targets a1 q0 δ vd e jmps).

Definition trace_state_res :=
  option (list (store_delta * option exit) * list ts_evidence).

Definition sat_evidences (evs: list ts_evidence) p h a0 s0 :=
  Forall (ts_evidence_proved p h a0 s0) evs.

(* TODO: remove redundant ts_evidences *)
Definition app_evidences (ev1 ev2: list ts_evidence) := ev1 ++ ev2.
Notation "ev1 !++ ev2" := (app_evidences ev1 ev2) (at level 60, right associativity).

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

Definition jump_hint := addr -> store_delta -> exp -> option (list jump_target).

Fixpoint simple_trace_stmt0 (hint: jump_hint) (vd: vdomain) (δ: store_delta)
  (a: addr) (q0: stmt) (q: stmt): trace_state_res :=
  match q with
  | Nop => Some ((δ, None) :: nil, nil)
  | Move v e => Some ((δ[[v := subst_exp vd δ e]], None) :: nil, nil)
  | Jmp e =>
      match hint a δ e with
      | Some jmps =>
          Some (flat_map (fun j =>
            match j with
            | jump_addr a => ((δ, Some (Exit a)) :: nil)
            | jump_symbolic => nil
            end) jmps, has_jump_targets a q0 δ vd e jmps :: nil)
      | None =>
          match subst_exp vd δ e with
          | Some (Word n _) => Some ((δ, Some (Exit n)) :: nil, nil)
          | _ => None
          end
      end
  | Exn n => Some ((δ, Some (Raise n)) :: nil, nil)
  | Seq q1 q2 =>
      match simple_trace_stmt0 hint vd δ a q0 q1 with
      | None => None
      | Some (paths1, ev1) =>
          let res := map_option (fun '(δ', x) =>
            match x with
            | None =>
                match simple_trace_stmt0 hint vd δ' a (Seq q0 q1) q2 with
                | None => None
                | Some (paths2, _) => Some paths2
                end
            | Some _ => Some ((δ', x) :: nil)
            end) paths1 in
          let ev' := flat_map (fun '(δ', x) =>
            match x with
            | None =>
                match simple_trace_stmt0 hint vd δ' a (Seq q0 q1) q2 with
                | None => nil
                | Some (_, ev2) => ev2
                end
            | Some _ => nil
            end) paths1 !++ ev1 in
          match res with
          | None => None
          | Some ll => Some (concat ll, ev')
          end
      end
  | If _ q1 q2 =>
      match simple_trace_stmt0 hint vd δ a q0 q1, simple_trace_stmt0 hint vd δ a q0 q2 with
      | None, _ | _, None => None
      | Some (paths1, ev1), Some (paths2, ev2) =>
          Some (paths1 ++ paths2, ev1 !++ ev2)
      end
  | Rep _ s => None
  end.

Theorem simple_trace_stmt0_correct: forall hints vd q q0 paths h p n
  a0 s0 s0' a1 s1 x2 s2 δ evs
  (HD: has_delta vd h s0 s1 δ) (XS: exec_stmt h s1 q s2 x2)
  (LU2: forall a2, x2 = Some (Exit a2) -> exists insn, p s2 a2 = Some insn)
  (STS: simple_trace_stmt0 hints vd δ a1 q0 q = Some (paths, evs))
  (XP: exec_prog h p a0 s0 n s0' (Exit a1)) (XS0: exec_stmt h s0' q0 s1 None)
  (EV: sat_evidences evs p h a0 s0),
  Exists (fun '(δ', x') => x' = x2 /\ has_delta vd h s0 s2 δ') paths.
Proof.
  induction q; intros; inversion XS; inversion STS; subst; clear STS.
  - (* Nop *) constructor. split; trivial2.
  - (* Move *) constructor. split. reflexivity. destruct subst_exp eqn: SE1;
    [|apply has_delta_assign_None; assumption]. apply has_delta_assign_Some.
    assumption. intros. eapply subst_exp_correct; eassumption.
  - (* Jmp *) destruct hints as [jmps|].
    + (* Use hint *) inversion H3. subst. clear H3. inversion EV. inversion H1.
      subst. einstantiate trivial EJT as EJT. apply Exists_exists in EJT.
      apply Exists_exists. einversion trivial LU2 as [insn LU'].
      destruct EJT as [j [InJmps EJ] ]. inversion EJ;
      [|rewrite LU in LU'; discriminate]. subst. clear EJ.
      eexists. split. apply in_flat_map. eexists. split; [eassumption|].
      simpl. left. reflexivity. simpl. split; trivial2.
    + (* No hint *) destruct (subst_exp _ _ _) eqn: SE; try destruct e0; inversion H3.
      subst. constructor. split; [|assumption].
      einstantiate trivial subst_exp_correct as Res. constructor. inversion Res.
      subst. reflexivity.
  - (* Exn *) constructor. split; trivial2.
  - (* Seq, exit 1 *) destruct simple_trace_stmt0 as [res1|] eqn: SQ1; try discriminate.
    destruct res1 as [paths1 ev1]. destruct map_option as [path_res|] eqn: Map;
    inversion H4. subst. clear XS H4. apply Forall_app in EV.
    destruct EV as [EV EV1]. einstantiate trivial IHq1. apply Exists_exists in H.
    destruct H as [ [δ1 x1] [InP1 [X HD1] ] ]; subst. apply Exists_exists.
    exists (δ1, Some x). repeat split; try assumption. apply in_concat. eexists.
    split; [|apply in_eq].  eapply map_option_includes; try eassumption. reflexivity.
  - (* Seq, exit 2 *) destruct simple_trace_stmt0 as [res1|] eqn:SQ1; [|discriminate].
    destruct res1 as [paths1 ev1]. destruct map_option as [path_res|] eqn: Map;
    inversion H4. subst. clear XS H4. apply Forall_app in EV. destruct EV as [EV EV1].
    einstantiate trivial IHq1. apply Exists_exists in H.
    destruct H as [ [δ1 x1] [InP1 [X HD1] ] ]; subst. apply Exists_exists.
    destruct (simple_trace_stmt0 hints vd δ1 a1 (q0 $; q1) q2) as [ [paths2 ev2]|] eqn:SQ2.
    + (* Expand out IHq2. We have to show that ev2 is part of ev' *)
      einstantiate trivial IHq2 as IHq2. econstructor; eassumption.
      unfold sat_evidences. rewrite Forall_forall in *. intros ev' InEV2.
      einstantiate trivial EV. apply in_flat_map. eexists. split. eassumption.
      simpl. rewrite SQ2. eassumption. rewrite Exists_exists in IHq2.
      destruct IHq2 as [ [δ' x'] [InP2 [EQ HD'] ] ]. subst.

      (* From IHq2, show that delta holds since the state is in (concat path_res) *)
      eexists. split. apply in_concat. eexists. split; [|eassumption].
      eapply map_option_includes; try eassumption. simpl. rewrite SQ2.
      reflexivity. simpl. split; trivial2.
    + erewrite map_option_fails in Map; try solve [discriminate|eassumption].
      simpl. rewrite SQ2. reflexivity.
  - (* If/else *) destruct c;
    (destruct (simple_trace_stmt0) as [ [paths1 ev1]|] eqn: ST1; [|discriminate]);
    (destruct (simple_trace_stmt0 _ _ _ _ _ q2) as [ [paths2 ev2]|] eqn: ST2;
        [|discriminate]); inversion H5; subst; apply Forall_app in EV;
    destruct EV.
    + (* q2 *) einstantiate trivial IHq2. eapply incl_Exists.
      apply incl_appr. apply incl_refl. assumption.
    + (* q1 *) einstantiate trivial IHq1. eapply incl_Exists.
      apply incl_appl. apply incl_refl. assumption.
Qed.

Definition simple_trace_stmt (hint: jump_hint) (vd: vdomain) (δ: store_delta)
  (a: addr) (q: stmt): trace_state_res :=
  match simple_trace_stmt0 hint vd δ a Nop q with
  | Some (next_states, evs) =>
      Some (map (fun '(δ, x) => (trim_delta_state vd δ, x)) next_states, evs)
  | None => None
  end.

Theorem simple_trace_stmt_correct: forall hints vd q paths h p n
  a0 s0 a1 s1 x2 s2 δ evs (XP: exec_prog h p a0 s0 n s1 (Exit a1))
  (HD: has_delta vd h s0 s1 δ) (XS: exec_stmt h s1 q s2 x2)
  (LU2: match x2 with
        | Some (Exit a2) => exists insn, p s2 a2 = Some insn
        | _ => True
        end)
  (STS: simple_trace_stmt hints vd δ a1 q = Some (paths, evs))
  (EV: sat_evidences evs p h a0 s0),
  Exists (fun '(δ', x') => x' = x2 /\ has_delta vd h s0 s2 δ') paths.
Proof.
  intros. unfold simple_trace_stmt in STS.
  destruct simple_trace_stmt0 as [ [next_states evs']|] eqn: STS0; try discriminate.
  inversion STS. subst. clear STS. einstantiate trivial simple_trace_stmt0_correct.
  intros. subst. assumption. constructor. rewrite Exists_exists in *.
  destruct H as [ [δ' x'] [InX [EQ HD0] ] ]. subst.
  eexists (_, x2). repeat split. eassert (X: (_, x2) = _ _);
    [|rewrite X; apply in_map; eassumption]. reflexivity.
  apply trim_delta_state_correct. assumption.
Qed.

Definition join_states_if_changed (vd: vdomain) (δ1: option store_delta)
  (δ2: store_delta): option store_delta :=
  match δ1 with
  | Some δ1 =>
      if delta_equivb vd δ1 δ2
      then None
      else let δ_merge := (fold_right (fun v δ' =>
        δ'[[v := if δ1<{vd}>[[v]] == δ2<{vd}>[[v]] then δ2<{vd}>[[v]] else None]])
        nil (delta_defined (δ1 ++ δ2))) in
        if delta_equivb vd δ1 δ_merge then
            None
        else
            Some δ_merge
  | None => Some δ2
  end.

Definition null_state: store := fun _ => VaN 0 0.

Definition process_state (vd: vdomain) (exitof: option exit -> exit)
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
      match join_states_if_changed vd (tget_n ts next_addr) δ' with
      | Some δ_merge => (tupdate_n ts next_addr δ_merge, true)
      | None => (ts, changed)
      end
  | Raise _ => (ts, changed)
  end.

Definition stmt_correct vd q δ x := forall s0 h s s' (XS: exec_stmt h s q s' x),
  has_delta vd h s0 s' δ.

Definition correctness_sub_prog vd p domain ts h a0 s0 :=
  (forall a1 s1 n1 δ
    (XP: exec_prog h (sub_prog p domain) a0 s0 n1 s1 (Exit a1))
    (TS2: tget_n ts a1 = Some δ), has_delta vd h s0 s1 δ).

Definition trace_program_step_at (vd: vdomain) (p: program)
  (hints: jump_hint) addr (accum: option (trace_states * bool * list ts_evidence)) :=
  match accum with
  | None => None
  | Some (ts, changed, old_evs) =>
      (* If this is a proper address in program, process that. Otherwise, this
       * is an invalid execution, so wouldn't happen to begin with. *)
      match p null_state addr with
      | None => Some (ts, changed, old_evs)
      | Some (sz, q) =>
          (* We have to had visited this address to begin with; otherwise, we
           * won't be able to push trace states for this address's successors. *)
          match tget_n ts addr with
          | None => Some (ts, changed, old_evs)
          | Some δ_a =>
              match simple_trace_stmt hints vd δ_a addr q with
              | None => None
              | Some (next_states, evs) =>
                  let res := fold_right (process_state vd
                    (exitof (addr + sz))) (ts, changed) next_states in
                  Some (res, evs !++ old_evs)
              end
          end
      end
  end.

Definition expand_trace_program (vd: vdomain) (p: program)
  (hints: jump_hint) (init_ts: trace_states):
  option (trace_states * bool * list ts_evidence) :=
  fold_right (trace_program_step_at vd p hints) (Some (init_ts, false, nil))
    (tkeys_n init_ts).

Definition iterM (n: N) {A} (f: A -> option A) (x: A) :=
  N.iter n (fun x => match x with Some x => f x | None => None end) (Some x).

Definition expand_trace_program_n (n: N) (vd: vdomain)
  (hints: jump_hint) (p: program) (init_ts: trace_states):
  option (trace_states * bool * list ts_evidence) :=
  N.iter n (fun x =>
    match x with
    | Some (ts, true, _) => expand_trace_program vd p hints ts
    | Some (ts, false, ev) => Some (ts, false, ev)
    | None => None
    end) (Some (init_ts, true, nil)).

Lemma fold_expand_trace_program: forall vd p hints init_ts,
  fold_right (trace_program_step_at vd p hints) (Some (init_ts, false, nil))
    (tkeys_n init_ts) = expand_trace_program vd p hints init_ts.
Proof. reflexivity. Qed.

(*
Theorem trace_program_step_at_steady_correct: forall vd p a_new al hints ts
  h a0 s0 (Init: forall δ s, tget_n ts a0 = Some δ -> has_delta vd h s s δ)
  (IHal: correctness_sub_prog vd p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
  (Total: Forall (fun a1 => exists δ1, tget_n ts a1 = Some δ1) (a_new :: al))
  (TPSA: trace_program_step_at vd p hints a_new (Some (ts, false)) =
    Some (ts, false))
  (HintsCorrect: forall a_new al ts h a0 s0
    (IHal: correctness_sub_prog vd p al ts h a0 s0) (UNIQ: NoDup (a_new :: al))
    (Total: Forall (fun a1 => exists δ1, tget_n ts a1 = Some δ1) (a_new :: al))
    (Hint: hints p a_new ts = Some (ts, false)),
    correctness_sub_prog vd p (a_new :: al) ts h a0 s0),
  correctness_sub_prog vd p (a_new :: al) ts h a0 s0.
Proof.
Admitted.
  (* Destruct trace_program_step_at function. *)
  unfold correctness_sub_prog. intros. simpl in TPSA.

  (* Using hint if available *)
  destruct hints as [ [ts' changed']|] eqn: Hint. inversion TPSA. subst.
  eapply HintsCorrect; try eassumption. clear HintsCorrect.

  destruct (p _ _) as [ [sz_new q_new]|] eqn: LUa_new; try discriminate.
  destruct (tget_n ts a_new) as [δ_a_new|] eqn: TSa_new; try discriminate.
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
    apply existsb_exists in EXa2. destruct EXa2 as [a1' [InDomain Eq] ].
    destruct (a1 == a1'); try discriminate. subst. assumption.
Admitted.
 *)

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

(*
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
  - (* Seq, exit in q1 *) destruct (stmt_reachable q1) as [ [j1 falls1]|] eqn: J1;
    try solve [destruct (stmt_reachable q2) eqn: J2; discriminate]. destruct falls1.
    + (* Can fall-through *) destruct x0; try reflexivity.
      destruct (stmt_reachable q2) as [ [j2 falls2]|] eqn: J2; try discriminate.
      inversion JMPS. subst. apply set_ap_has_l. einstantiate trivial IHq1.
    + (* Cannot fall-through *) inversion JMPS. subst. destruct x0;
      try reflexivity. einstantiate trivial IHq1.
  - (* Seq, exit in q2 *) destruct (stmt_reachable q1) as [ [j1 falls1]|] eqn: J1;
    try solve [destruct (stmt_reachable q2) eqn: J2; discriminate]. destruct falls1.
    + (* Can fall-through *) destruct (stmt_reachable q2) as [ [j2 falls2]|] eqn: J2;
      try discriminate. inversion JMPS. subst. einstantiate trivial IHq2 as IHq2.
      destruct x as [ [a|n]|]; trivial2. apply set_ap_has_r. assumption.
    + (* Cannot fall-through; contradiction *) inversion JMPS.
      subst. einstantiate trivial IHq1 as IHq1.
  - (* If *) destruct (stmt_reachable q1) as [ [j1 falls1]|] eqn: J1;
    destruct (stmt_reachable q2) as [ [j2 falls2]|] eqn: J2; try discriminate.
    inversion JMPS. subst. clear JMPS. destruct x as [ [a|n]|]; try reflexivity.
    + (* Jumped *) rewrite set_ap_has_split. apply orb_true_intro.
      destruct c; [einstantiate trivial IHq2; right|
        einstantiate trivial IHq1; left]; eassumption.
    + (* Fallthrough *) apply orb_true_intro. destruct c;
      [einstantiate trivial IHq2; right | einstantiate trivial IHq1; left];
      assumption.
  - (* Evil rep *) destruct stmt_reachable as [ [jmps' falls']|] eqn: Jinner;
    inversion JMPS. subst. destruct x as [ [a|?]|]; try reflexivity.
    einstantiate trivial rep_exits_total as RET.
    destruct RET as [s2 [s2' XSinner] ]. einstantiate trivial IHq.
Qed.

Lemma reachables_incl: forall hints p a reaches' reaches
  (RA: reachables_at hints p a (Some reaches) = Some reaches'),
  incl (set_elems reaches) (set_elems reaches').
Proof.
  unfold reachables_at. intros. destruct hints eqn: Hints.
  - inversion RA. subst. intros a2 InS. apply set_ap_right. assumption.
  - destruct p as [ [sz q]|] eqn: LU; try discriminate.
    destruct stmt_reachable as [ [jmps falls]|] eqn: SRQ; try discriminate.
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
  destruct p as [ [sz q]|] eqn: LU; try discriminate.
  destruct stmt_reachable as [ [sjmps falls]|] eqn: SR; inversion RA. subst.
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
        rewrite <- RA'. destruct x' as [ [a|?]|]; try inversion EX; subst.
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
  destruct x as [ [r fin]|]; try discriminate.
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
 *)

Require Import Picinae_i386.
Require Import strchr_i386.
Import X86Notations.

Definition fh := htotal.

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

Definition simp_prog_jump_hints: jump_hint := fun a δ e => None.

Definition simp_prog_trace := expand_trace_program_n 10 (fun _ => true)
  simp_prog_jump_hints simp_prog (tupdate_n treeN_nil 0 nil).

Goal True.
Proof.

  pose (x := match simp_prog_trace with
             | Some (ts, b, ev) =>
                 match tget_n ts 1 with
                 | Some δ => Some (ts, δ, b, ev)
                 | None => None
                 end
             | None => None
             end).
  compute in x.
Abort.

Require Import test.
Theorem my_prog_welltyped: welltyped_prog x86typctx my_prog.
Proof.
  Picinae_typecheck.
Qed.

Definition my_prog_jump_hints: jump_hint := fun a δ e =>
  match a with
  | 34 => Some (jump_symbolic :: nil)
  | _ => None
  end.

Definition domain1 var :=
  match var with
  | V_TEMP _ => false
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => false
  | _ => true
  end.

Definition my_prog_trace x := expand_trace_program_n x domain1
  my_prog_jump_hints my_prog (tupdate_n treeN_nil 0 nil).

Ltac unbox_res v :=
  match eval red in v with
  | Some (?v', _) => clear v; pose (v := v')
  end.

Ltac unbox_Some v :=
  match eval red in v with
  | Some ?v' => clear v; pose (v := v')
  end.
Goal forall esp0 s0 (MDL0: models x86typctx s0)
  (SV2: s0 R_ESP = Ⓓ esp0),
  exists val,
  eval_exp fh (s0 [ R_ESP := Ⓓ  42 ] [A_READ := Ⓜ (fun _ => 1)]
    [A_WRITE := Ⓜ (fun _ => 1)])
  (Load
     (Store
        (Store (Var V_MEM32) (BinOp OP_MINUS (Var R_ESP) (Word 4 32))
           (Cast CAST_LOW 32 (Var R_EBP)) LittleE 4)
        (BinOp OP_PLUS (BinOp OP_MINUS (Var R_ESP) (Word 4 32))
           (Word 4294967292 32)) (Word 0 32) LittleE 4)
     (BinOp OP_PLUS (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) (Word 4 32))
     LittleE 4) val.
Proof.
  intros.
  assert (MDL': models x86typctx (s0 [ R_ESP := Ⓓ  42 ] [A_READ := Ⓜ (fun _ => 1)]
    [A_WRITE := Ⓜ (fun _ => 1)])).
    intros v t eq. destruct v; psimpl;
    try solve [ eapply MDL0; eassumption
              | einversion eq; constructor; try intro; reflexivity].

  match goal with |- exists u, eval_exp ?h ?s ?e u =>
      mk_eval_exp h s e EE
  end.

  repeat split; try reflexivity; unfold mem_readable, mem_writable; psimpl;
  eexists; (split; [reflexivity|intro Contra; discriminate]).

  eexists. exact EE.
Qed.

Ltac concretize_delta HD v :=
  lazymatch type of HD with has_delta ?vd ?h ?s0 ?s1 ?δ =>
  lazymatch eval compute in (δ<{vd}>[[v]]) with
  | Some ?e =>
      let EE := fresh in
      mk_eval_exp h s0 e EE; [|
          let SV := fresh "Hsv" in
          einstantiate trivial (HD v) as SV; clear EE]
  | None => fail "Unknown value for " v
  end
  end.

Require Import mod_arith.

Theorem getmem_frame_absdist: forall e1 e2 len1 len2 m a1 a2 v,
  len1 <= absdist a1 a2 -> len2 <= absdist a1 a2 ->
  getmem e1 len1 (setmem e2 len2 m a2 v) a1 = getmem e1 len1 m a1.
Proof.
  unfold absdist. intros. destruct (_ <=? _) eqn: LE.
  - apply N.leb_le in LE. specialize (conv_le_add_le_sub_r _ _ _ H LE). intro.
    apply getmem_frame_low. rewrite N.add_comm. assumption.
  - apply not_true_iff_false in LE. assert (a2 < a1).
    apply N.lt_nge. revert LE. contrapositive N.leb_le.
    apply getmem_frame_high. rewrite N.add_comm. apply conv_le_add_le_sub_r.
    assumption. intros X. rewrite H1 in X. discriminate.
Qed.

Theorem my_prog_nwc: forall s2 s1, my_prog s1 = my_prog s2.
Proof. reflexivity. Qed.

Theorem my_prog_hints_correct: forall esp0 mem s0 ts evs
  (ESP0: s0 R_ESP = Ⓓ esp0) (MEM0: s0 V_MEM32 = Ⓜmem) (ESP_BIG: 8 <= esp0)
  (RET: my_prog s0 (mem Ⓓ[ esp0 ]) = None) (WM: forall s0, s0 A_WRITE = Ⓜ (fun _ => 1))
  (RM: forall s0, s0 A_READ = Ⓜ (fun _ => 1))
  (MDL0: models x86typctx s0) (MPT: my_prog_trace 100 = Some (ts, false, evs)),
  sat_evidences evs my_prog fh 0 s0.
Proof.
  intros. vm_compute in MPT. inversion MPT. subst. clear MPT.
  repeat constructor. eassert (MDL': models _ s1).
    eapply preservation_exec_stmt; [| |exact XS0].
    eapply preservation_exec_prog; [|exact my_prog_welltyped|]; eassumption.
    eapply typchk_stmt_sound; reflexivity. simpl in MDL'.

  step_stmt XS. destruct XS as [ [? ?] ? ]. inversion H0. subst.

  concretize_delta HD (V_TEMP 6).

  (* Prove memory accesses *)
  repeat split; try reflexivity; unfold mem_readable, mem_writable; psimpl;
  eexists; (split; [apply WM + apply RM|intro Contra; discriminate]).

  psimpl in Hsv1. rewrite Hsv1 in Hsv. remember (2 ^ 32). inversion Hsv.
  subst. repeat unsimpl (getmem LittleE 4 _ _). repeat unsimpl (setmem LittleE 4 _ _).
  specialize (x86_regsize MDL0 ESP0) as ESP_BND. cbv beta match delta [x86typctx] in ESP_BND.

  assert (4 <= 2 ^ 32 + esp0). apply le_le_add_r. discriminate.
  assert (EQ_ESP0: 2 ^ 32 + esp0 - 4 ⊕ 4 = esp0).
  rewrite <- N.add_sub_swap, <- N.add_sub_assoc, N.sub_diag, N.add_0_r,
    N.add_mod, N.mod_same, N.add_0_l, N.mod_mod, N.mod_small by trivial2.
  reflexivity. rewrite EQ_ESP0.

  (* Figure the modular arithmetic stuff *)
  assert (2 ^ 32 - 4 ⊕ esp0 < 2 ^ 32). apply N.mod_lt. discriminate.
  assert (2 ^ 32 - 4 + esp0 ⊕ 4294967292 < 2 ^ 32). apply N.mod_lt. discriminate.
  assert (4 <= absdist esp0 (2 ^ 32 + esp0 ⊖ 4)).
    erewrite N.add_sub_swap, <- modabsdist_eq_absdist, modr_modabsdist by trivial2.
    einversion trivial (modabsdist_add_l (2 ^ 32)) as [MAD|MAD];
        rewrite MAD; discriminate.
  assert (4 <= absdist esp0 (2 ^ 32 + esp0 - 4 ⊕ 4294967292)).
    erewrite N.add_sub_swap, <- modabsdist_eq_absdist, modr_modabsdist by trivial2.
    rewrite <- N.add_assoc, (N.add_comm esp0), N.add_assoc.
    einversion trivial (modabsdist_add_l (2 ^ 32)) as [MAD|MAD];
        rewrite MAD; discriminate.

  repeat rewrite getmem_frame_absdist; trivial2.
Qed.

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

Definition strchr_reachables_hint (ret: addr) (a: addr): option set :=
  match a with
  | 401 => Some {{ret}}
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

Require Extraction.
Extraction Language OCaml.

Definition strchr_trace reachables := expand_trace_program_n 100 (fun _ => true)
  strchr_trace_hint strchr_i386 reachables (tupdate_n treeN_nil 0 nil).

Definition strchr_trace2 reachables := expand_trace_program_n 100 domain1
  strchr_trace_hint strchr_i386 reachables (tupdate_n treeN_nil 0 nil).

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Require Import ExtrOcamlIntConv.
Extraction "calling" strchr_trace strchr_trace2 strchr_reachables list_to_set
  n_of_int int_of_n.

Goal True.
Proof.
  idtac "DOING STRCHR_TRACE".

  pose (x := strchr_reachables 0).
  compute in x.
  match eval compute in x with
  | Some (?v, nil) => clear x; pose (reachables := v)
  end.
  pose (x := strchr_trace2 (list_to_set reachables)).
  time (vm_compute in x). unbox_res x.

  pose (y := tget_n x 401); compute in y.

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
