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

(* We define a store delta as a  *)
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
  | Let v e e_in => false
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
  | Let v e e_in => Unknown 0 (* Error *)
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
             | IH: forall (DNU: delta_nounk δ), _ |- _ => idtac IH;
                 einstantiate trivial IH as IH
             end
  end.

Theorem subst_exp0_nounk: forall e δ (DNU: delta_nounk δ)
  (SE: subst_valid δ e = true), forall_exps_in_exp not_unknown (subst_exp0 δ e).
Proof.
  unfold subst_exp; induction e; intros; simpl in SE;
  try solve [exp_destruction_nounk; repeat split; assumption + reflexivity].

  (* Var *) destruct (δ v) eqn: LUv; inversion SE. subst. eapply DNU. simpl.
  rewrite LUv. reflexivity.
Qed.

Theorem subst_exp_nounk: forall e e' δ (DNU: delta_nounk δ)
  (SE: subst_exp δ e = Some e'), forall_exps_in_exp not_unknown e'.
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

Theorem subst_exp_correct: forall s0 h e e' s δ v v'
  (HD: has_delta h s0 s δ) (SE: subst_exp δ e = Some e') (EE: eval_exp h s e v)
  (EE': eval_exp h s0 e' v'), v = v'.
Proof.

  intros. move δ before e. repeat lazymatch goal with H:_ |- _ => revert H end.

  unfold subst_exp; induction e; intros; inversion EE; subst;
  simpl in SE; clear EE; try solve [exp_destruction_correct; reflexivity].
  - (* Var *) destruct (δ v) eqn: LUv; inversion SE. subst. erewrite HD;
    solve [reflexivity|eassumption].
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
  (accum: (addr -> option store_delta) * bool) (st: store_delta * option exit) :=
  let '(fδ', changed) := accum in
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
      match join_states_if_changed vars (fδ' next_addr) δ' with
      | Some δ_merge => (update fδ' next_addr (Some δ_merge), true)
      | None => (fδ', changed)
      end
  | Raise _ => (fδ', changed)
  end.

Definition trace_program_step_at (vars: list var)

Definition dependent_correctness h p a0 s0 fδ a working conds := forall a1,
  (Exists (fun w => reachable_thru h p a0 s0 w a1) working) \/
  (forall s1 n1 δ (XP1: exec_prog h p a0 s0 n1 s1 (Exit a1))
    (LUdelta: fδ a1 = Some δ), has_delta' s0 s1 δ conds).

Theorem process_state_correct: forall q sz h vars p a0 s0 a
  next_states st' fδ fδ' δ working new_working conds
  (SS: incl st' next_states)
  (NWC: forall s1 s2, p s1 = p s2)
  (* TODO: something for domain_complete *)
  (LUa: fδ a = Some δ) (PA: p null_state a = Some (sz, q))
  (PS: process_state vars (exitof (a + sz)))
  (IHfδ: state_correctness h p a0 s0 fδ (a :: working) conds),
  state_correctness h p a0 s0 fδ' working' (h_conj conds P').
Proof.
Abort.

Definition trace_program_step (vars: list var) (p: program) (tsp: trace_states_prop)
  (fn: store_delta -> stmt -> trace_state_res_with_prop): option trace_states_prop :=
  let '((fδ, working), P) := tsp in
  (* Extract first address in the working set. Otherwise just terminate with
   * steady state *)
  match working with
  | nil => Some tsp
  | a :: working =>
      (* If this is a proper address in program, process that. *)
      match p null_state a with
      (* TODO: implement calls for here. This happens when we reached a none
       * spot. *)
      | None => None (*Some (fδ, working, P)*)
      | Some (sz, q) =>
          (* Check if the statement tracer can handle this type of statement.
           * If it can't, then we terminate on error *)
          match fδ a with
          | None => None
          | Some δ_a =>
              match fn δ_a q with
              | None => None
              | Some (next_states, P') =>
                  (* Iterate through the set of next_states, merging states that we
                   * currently have for these addresses and what the tracer
                   * generated. *)
                  let '(fδ', new_working) := fold_left (process_state vars
                    (exitof (a + sz))) next_states (fδ, nil) in
                  Some ((fδ', working ++ new_working), h_conj P P')
              end
          end
      end
  end.

Definition init_store_delta (c: typctx): store_delta :=
  fun v =>
    match c v with
    | Some (NumT w) => VarOff v 0 w
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
      match get_jumps q with
      | Some jmps =>
          fold_left
          set_add jmps (a + sz)
      | None => None
  | None => None.

Fixpoint get_reachable (p: program) (a: addr) :=
  get_jumps
