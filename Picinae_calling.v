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

Inductive simple_exp :=
  | Number (n: N) (w: bitwidth)
  | VarOff (v: var) (off: N) (w: bitwidth)
  | Complex.

Definition store_delta := var -> simple_exp.

Definition sexp_width (e: simple_exp) :=
  match e with
  | Number _ w => Some w
  | VarOff _ _ w => Some w
  | Complex => None
  end.

Inductive hastyp_simple_exp (c0: typctx): simple_exp -> typ -> Prop :=
  | TSE_Num (n: N) (w: bitwidth) (LT: n < 2 ^ w):
      hastyp_simple_exp c0 (Number n w) (NumT w)
  | TSE_VarOff (v: var) (w: bitwidth) (off: N) (CV: c0 v = Some (NumT w))
      (LT: off < 2 ^ w): hastyp_simple_exp c0 (VarOff v off w) (NumT w).

Inductive eval_simple_exp (s: store): simple_exp -> value -> Prop :=
  | ESE_Number n w: eval_simple_exp s (Number n w) (VaN n w)
  | ESE_VarOff v n off w (SV: s v = VaN n w): eval_simple_exp s
      (VarOff v off w) (VaN ((n + off) mod 2 ^ w) w).

Definition has_delta (s s': store) (δ: store_delta) :=
  forall v val (ESE: eval_simple_exp s (δ v) val), s' v = val.

Definition safety (c0: typctx) (se: simple_exp) :=
  forall v0 off w (EQ_V: se = VarOff v0 off w), c0 v0 = Some (NumT w).

Definition delta_safety (c0: typctx) (δ: store_delta) :=
  forall v, safety c0 (δ v).

Definition delta_models (c0 c: typctx) (δ: store_delta) :=
  forall v t (CV: c v = Some t) (NotCpx: δ v <> Complex), hastyp_simple_exp c0 (δ v) t.

Lemma hastyp_simple_exp_num:
  forall c0 e t (TSE: hastyp_simple_exp c0 e t), exists w, t = NumT w.
Proof.
  intros. inversion TSE; eexists; reflexivity.
Qed.

Fixpoint simplify_exp (δ: store_delta) e :=
  match e with
  | Var v => δ v
  | Word n w => Number n w
  | Load _ _ _ _ => Complex
  | Store _ _ _ _ _ => Complex
  | BinOp op e1 e2 =>
      let of_oper w v offset n (is_inverted: bool) :=
        match op with
        | OP_PLUS => if is_inverted then
            VarOff v ((n + offset) mod 2 ^ w) w
          else
            VarOff v ((offset + n) mod 2 ^ w) w
        | OP_MINUS => if is_inverted then Complex else
            VarOff v ((offset + 2 ^ w - n) mod 2 ^ w) w
        | _ => Complex
        end in
      match simplify_exp δ e1, simplify_exp δ e2 with
      | Complex, _ | _, Complex | VarOff _ _ _, VarOff _ _ _ => Complex
      | Number n1 w1, Number n2 w2 =>
          if w1 == w2 then
            match eval_binop op w1 n1 n2 with
            | VaN n w' => Number n w'
            | VaM _ _ => Complex
            end
          else Complex
      | VarOff v1 off1 w1, Number n2 w2 =>
          if w1 == w2 then of_oper w1 v1 off1 n2 false
          else Complex
      | Number n1 w1, VarOff v2 off2 w2 =>
          if w1 == w2 then of_oper w1 v2 off2 n1 true
          else Complex
      end
  | UnOp _ _ => Complex
  | Cast typ w' e =>
      let se := simplify_exp δ e in
      match sexp_width se with
      | Some w =>
          match se with
          | Number n _ => Number (cast typ w w' n) w'
          | VarOff _ _ _ =>
              match typ with
              | CAST_LOW | CAST_HIGH => (* narrowing *)
                  if w <=? w' then se else Complex
              | CAST_UNSIGNED | CAST_SIGNED => (* widening *)
                  if w' <=? w then se else Complex
              end
          | Complex => Complex
          end
      | None => Complex
      end
  | Let v e e_in => simplify_exp (update δ v (simplify_exp δ e)) e_in
  | Unknown _ => Complex
  | Ite _ _ _ => Complex
  | Extract _ _ _ => Complex
  | Concat _ _ => Complex
  end.

Ltac einst0 H tac :=
  (lazymatch type of H with
   | ?t1 -> ?t2 =>
       let H0 := fresh in
       assert (H0: t1); [clear H|specialize (H H0); clear H0; einst0 H tac]
   | forall v, @?F v => epose proof (H ?[?v]) as H; einst0 H tac
   | _ => tac
   end).

Tactic Notation "einversion" constr(H) :=
  let Htmp := fresh in
  pose proof H as Htmp; einst0 Htmp ltac:(inversion Htmp; clear Htmp; subst).

Tactic Notation "einversion" "trivial" constr(H) :=
  einversion H; try solve [eassumption|discriminate|reflexivity]; subst.

Tactic Notation "einstantiate" constr(H) :=
  let Htmp := fresh in
  pose proof H as Htmp; einst0 Htmp ltac:(idtac).

Tactic Notation "einstantiate" "trivial" constr(H) :=
  einstantiate H; try solve [eassumption|discriminate|reflexivity]; subst.

Ltac invalid H := contradiction H; reflexivity.

Lemma sexp_width_type_correct: forall c0 e w (TSE: hastyp_simple_exp c0 e (NumT w)),
  sexp_width e = Some w.
Proof.
  intros. inversion TSE; reflexivity.
Qed.

Lemma eval_simple_exp_num: forall s se v (ESE: eval_simple_exp s se v),
  exists n w, v = VaN n w.
Proof.
  intros. inversion ESE; subst; clear ESE; eexists; eexists; reflexivity.
Qed.

Lemma eval_simple_exp_total: forall s0 c0 se (Safe: safety c0 se)
  (MDL0: models c0 s0) (NCPX: se <> Complex), exists u, eval_simple_exp s0 se u.
Proof.
  intros. destruct se.
  - eexists. constructor.
  - einversion (MDL0 v); try (eapply Safe; reflexivity); inversion H2. subst.
    eexists. constructor. symmetry. eassumption.
  - invalid NCPX.
Qed.

Theorem simplify_eval_binop_destruct: forall (P: simple_exp -> Prop) se op e1 e2 δ
  (SE: se = simplify_exp δ (BinOp op e1 e2))
  (Complex: forall (EQ: se = Complex), P se)
  (ImmOpImm: forall w w' n' n1 n2 (EQ: se = Number n' w')
    (SE1: simplify_exp δ e1 = Number n1 w)
    (SE2: simplify_exp δ e2 = Number n2 w)
    (EBO: eval_binop op w n1 n2 = VaN n' w'), P se)
  (ImmPlusVar: forall w n v off (EQ: se = VarOff v ((n + off) mod 2 ^ w) w)
    (OP: op = OP_PLUS) (SE1: simplify_exp δ e1 = Number n w)
    (SE2: simplify_exp δ e2 = VarOff v off w), P se)
  (VarPlusImm: forall w n v off (EQ: se = VarOff v ((off + n) mod 2 ^ w) w)
    (OP: op = OP_PLUS) (SE1: simplify_exp δ e1 = VarOff v off w)
    (SE2: simplify_exp δ e2 = Number n w), P se)
  (VarMinusImm: forall w n v off (EQ: se = VarOff v ((off + 2 ^ w - n) mod 2 ^ w) w)
    (OP: op = OP_MINUS) (SE1: simplify_exp δ e1 = VarOff v off w)
    (SE2: simplify_exp δ e2 = Number n w), P se),
  P se.
Proof.
  intros. subst. simpl in *.
  Local Ltac hyp :=
    try match goal with
        | [H: _ |- _] => solve [eapply H; (reflexivity + eassumption)]
        end.
  destruct (simplify_exp _ e1) eqn: SE1; try hyp;
  destruct (simplify_exp _ e2) eqn: SE2; try hyp;
  destruct (_ == _) eqn: EQB; try hyp.
  - (* imm *) destruct (eval_binop _ _ _ _) eqn: EBO. subst. hyp. hyp.
  - (* imm OP var *) destruct op; hyp. subst. hyp.
  - (* var OP imm *) destruct op; hyp; subst; hyp.
Qed.

Tactic Notation "destruct_ext" uconstr(exp) :=
  let SE := fresh "SE" in
  let se := fresh "se" in
  remember exp as se eqn: SE; pattern se; eapply simplify_eval_binop_destruct;
  try exact SE; intros; move SE at bottom; subst.

Lemma simplify_eval_imp_no_complex: forall e δ s0 vs
  (ESE: eval_simple_exp s0 (simplify_exp δ e) vs),
  simplify_exp δ e <> Complex.
Proof.
  intros. destruct (simplify_exp _ _); solve [inversion ESE|discriminate].
Qed.

Lemma eval_simple_exp_unique: forall se s0 v1 v2
  (ESE1: eval_simple_exp s0 se v1) (ESE2: eval_simple_exp s0 se v2),
  v1 = v2.
Proof.
  intros. inversion ESE1; inversion ESE2; subst; inversion H1; subst.
  reflexivity. rewrite SV0 in SV. inversion SV. subst. reflexivity.
Qed.

Lemma neq_sym: forall A (n m: A), n <> m -> m <> n.
Proof.
  intros. intro. subst. apply H. reflexivity.
Qed.

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

Lemma has_delta_assign: forall s s' δ v se u (HD: has_delta s s' δ)
  (ESE: se = Complex \/ eval_simple_exp s se u),
  has_delta s (s' [v := u]) (δ [v := se]).
Proof.
  unfold has_delta. intros.
  destruct (v == v0).
  - subst. rewrite update_updated. rewrite update_updated in ESE0.
    destruct ESE; subst. try solve [inversion ESE0].
    eapply eval_simple_exp_unique; eassumption.
  - apply neq_sym in n. rewrite update_frame in ESE0 by assumption.
    rewrite update_frame in * by assumption. apply HD. assumption.
Qed.

Lemma safety_simplify_exp: forall c0 e δ
  (DS: delta_safety c0 δ), safety c0 (simplify_exp δ e).
Proof.
  unfold safety. induction e; intros; try discriminate.
  - (* Var *) eapply DS. eassumption.
  - (* Binop *) destruct_ext (simplify_exp _ (BinOp _ _ _));
    solve [ discriminate
          | inversion EQ; subst; (eapply IHe1 + eapply IHe2); eassumption ].
  - (* Cast *) simpl in *.
    destruct (sexp_width _) eqn: SEW; try discriminate.
    destruct (simplify_exp _) eqn: SE1; try discriminate.
    destruct c; destruct (_ <=? _) eqn: LEB; try discriminate;
    apply N.leb_le in LEB; simpl in SEW; inversion SEW; inversion EQ_V;
    subst; clear SEW EQ_V; eapply IHe; eassumption.
  - (* Let *)
    eassert (DS': delta_safety c0 (δ [v := _])). eapply delta_safety_assign.
    eassumption. unfold safety. eapply IHe1. eassumption.

    simpl in *; destruct (simplify_exp _ e1) eqn: SE1; try discriminate;
    eapply (IHe2 (δ[_ := _])); eassumption.
Qed.

Theorem preservation_simplify_exp: forall c0 e δ c s0 t vs
  (DS: delta_safety c0 δ) (ETyp: hastyp_exp c e t) (DMDL: delta_models c0 c δ)
  (ESE: eval_simple_exp s0 (simplify_exp δ e) vs),
  hastyp_simple_exp c0 (simplify_exp δ e) t.
Proof.
  intros. apply simplify_eval_imp_no_complex in ESE. clear s0 vs.
  repeat match goal with [H: _ |- _] => revert H end.
  induction e; intros; try invalid ESE.
  - (* Var *) inversion ETyp. subst. clear ETyp. simpl in *. apply DMDL in CV.
    destruct (δ v) eqn: Dv; try invalid ESE; einversion trivial CV; subst. constructor.
    assumption. constructor; [eapply DS|]; eassumption.
  - (* Word *) inversion ETyp. simpl. constructor. assumption.
  - (* Binop *) inversion ETyp. subst. clear ETyp.
    specialize (IHe1 δ). specialize (IHe2 δ).

    (* This is a common assumption that we will have to make *)
    assert (2 ^ w <> 0). destruct w; discriminate.

    destruct_ext (simplify_exp _ (BinOp _ _ _)); try invalid ESE;

    (* Push inductive hypothesis *)
    rewrite SE1 in *; rewrite SE2 in *;
    einversion trivial IHe1; einversion trivial IHe2;
    inversion H4; try inversion H8; subst;
    clear IHe1 IHe2 SE; simpl in *.

    (* imm OP imm *)
    eassert (TV: hastyp_val (eval_binop _ _ _ _) _). eapply typesafe_binop;
    constructor; [apply LT|apply LT0]. inversion TV. rewrite EBO in H1.
    inversion H1. subst. constructor. assumption.

    all: constructor; try assumption; apply N.mod_lt; assumption.
  - (* Cast *) inversion ETyp. subst. simpl in *.
    destruct (simplify_exp _ _) eqn: SE; try invalid ESE;
    (* Push inductive hypothesis *)
    (eassert (TSE: hastyp_simple_exp _ _ _);
      [eapply IHe; try eassumption; rewrite SE; discriminate|]);
    rewrite SE in *; inversion TSE; subst; clear TSE IHe; subst; simpl in *.

    (* Imm *)
    constructor. eassert (TV: hastyp_val (VaN (cast _ _ _ _) _) _).
    apply typesafe_cast. constructor. eassumption. eassumption.
    inversion TV. subst. assumption.

    (* Var *)
    destruct c; destruct (_ <=? _) eqn: LEB; try invalid ESE;
    apply N.leb_le in LEB; einversion trivial N.le_antisymm;
    constructor; assumption.
  - (* Let *) inversion ETyp. subst. clear ETyp. simpl in *.
    eassert (DS': delta_safety c0 (δ [v := _])).
      apply delta_safety_assign, safety_simplify_exp; eassumption.
    eassert (DMDL': delta_models c0 (c [v := _]) (δ [v := _])). {
      apply delta_models_assign. assumption.
      destruct (simplify_exp δ e1) eqn: SE1.
      + right. eapply (IHe1 δ c); try eassumption. rewrite SE1. discriminate.
      + right. eapply (IHe1 δ c); try eassumption. rewrite SE1. discriminate.
      + left. assumption.
    }

    destruct (simplify_exp _ e1) eqn: SE1; try invalid ESE; rewrite <- SE1 in *;
    eapply IHe2; try eassumption.
Qed.

Theorem simplify_exp_correct: forall e h s0 s c0 c δ vs ve t
  (ETyp: hastyp_exp c e t) (MDL0: models c0 s0) (MDL: models c s)
  (DS: delta_safety c0 δ) (DMDL: delta_models c0 c δ) (HD: has_delta s0 s δ)
  (EE: eval_exp h s e ve) (ESE: eval_simple_exp s0 (simplify_exp δ e) vs), ve = vs.
Proof.
  intros.

  (* Specify vs *)
  apply eval_simple_exp_num in ESE as VS. destruct VS as [n' [w' ?]]. subst.

  revert c s δ n' w' ve t MDL DMDL DS HD ETyp EE ESE.
  induction e; intros; try solve [inversion ESE].
  - (* Var *) inversion EE. subst. eapply HD. eassumption.
  - (* Word *) inversion EE. inversion ESE. subst. reflexivity.
  - (* BinOp *) inversion EE. inversion ETyp. subst. clear EE ETyp.

    (* Clean up some of the bitwidth variables, to ensure w = w0 *)
    assert (TV1 := preservation_eval_exp MDL T1 E1).
    assert (TV2 := preservation_eval_exp MDL T2 E2).
    epose proof (preservation_simplify_exp c0 e1 δ) as TSE1.
    epose proof (preservation_simplify_exp c0 e2 δ) as TSE2.
    inversion TV1. inversion TV2. subst. clear TV1 TV2 H5.

    (* This is a common assumption that we will have to make *)
    assert (2 ^ w0 <> 0). destruct w0; discriminate.

    (* Do a bunch of case destructions *)
    destruct_ext (simplify_exp _ (BinOp _ _ _)); inversion ESE; subst; clear ESE;

    (* Inversion on inductive hypothesis *)
    einversion trivial IHe1; try solve [rewrite SE1; constructor; eassumption];
    einversion trivial IHe2; try solve [rewrite SE2; constructor; eassumption];
    inversion H2; inversion H3; subst; clear H2 H3 H6 IHe1; simpl;

    (* imm OP imm is trivial*)
    try assumption;

    (* Ensure that n0 < 2 ^ w' *)
    rewrite SE2, SE1 in *; einversion trivial TSE1; try solve [econstructor|constructor; eassumption];
    einversion trivial TSE2; try solve [econstructor|constructor; eassumption]; subst;
    einversion trivial (MDL0 v); try eassumption; rewrite SV in H2; inversion H2;
    subst; clear TSE1 TSE2.

    (* imm + var *)
    erewrite <- (N.mod_small n) at 1 by eassumption.
    erewrite <- (N.mod_small n0) at -1 by eassumption.
    repeat rewrite <- N.add_mod by assumption. f_equal. f_equal.
    rewrite N.add_assoc, N.add_assoc. f_equal. apply N.add_comm.

    (* var + imm *)
    erewrite <- (N.mod_small n) at 1 by eassumption.
    erewrite <- (N.mod_small n0) at -1; [|eassumption].
    repeat rewrite <- N.add_mod by assumption. f_equal. f_equal.
    rewrite N.add_assoc. reflexivity.

    (* var - imm *)
    rewrite N.add_comm. f_equal.
    apply N.lt_le_incl in LT0. rewrite <- N.add_sub_assoc, <- N.add_sub_assoc,
      N.add_mod, N.mod_mod, <- N.add_mod, (N.add_mod n0), N.mod_mod,
    <- N.add_mod, N.add_assoc by assumption. reflexivity.
  - (* Cast *) inversion EE. inversion ETyp. subst. simpl in ESE.
    assert (X: 2 ^ w' <> 0). destruct w'; discriminate.

    destruct (simplify_exp δ e) eqn:Se; try solve [inversion ESE].

    (* imm *)
    inversion ESE. subst. f_equal. simpl in ESE. einversion trivial IHe.
    rewrite Se. econstructor. inversion H1. subst. reflexivity.

    (* var off *)
    simpl in ESE.
    destruct c; destruct (_ <=? _) eqn: LEB; inversion ESE; subst;
    einversion trivial @preservation_eval_exp; inversion H1;
    inversion H2; subst; rewrite <- Se in ESE; einversion trivial IHe;
    inversion H3; subst; rewrite N.leb_le in LEB;
    einversion trivial N.le_antisymm; simpl.
    + (* CAST_LOW *) rewrite N.mod_mod by assumption. reflexivity.
    + (* CAST_HIGH *) rewrite N.sub_diag. simpl. reflexivity.
    + (* CAST_SIGNED *) unfold scast. rewrite ofZ_toZ, N.mod_mod. reflexivity.
      assumption.
    + (* CAST_UNSIGNED *) reflexivity.
  - (* Let *) inversion EE. inversion ETyp. simpl in ESE. subst.
    assert (SV: forall v0 off w, simplify_exp δ e1 = VarOff v0 off w ->
      exists n, s0 v0 = VaN n w).
    { intros. einversion (MDL0 v0). eapply safety_simplify_exp; eassumption.
      all: inversion H3. eexists. reflexivity. }

    eapply IHe2; try apply ESE; try apply E2; try apply T2.

    (* MDL' *) eapply models_assign; eassumption.
    (* DMDL' *) {
      apply delta_models_assign; try assumption.
      destruct (simplify_exp _ e1) eqn: SE1.
      - right. rewrite <- SE1 in *. eapply preservation_simplify_exp;
        try eassumption. rewrite SE1. constructor.
      - right. rewrite <- SE1 in *. einversion trivial SV.
        eapply preservation_simplify_exp; try eassumption. rewrite SE1.
        constructor. eassumption.
      - left. reflexivity.
    }
    (* DS' *) apply delta_safety_assign; try assumption.
    apply safety_simplify_exp. assumption.
    (* HD' *) {
      apply has_delta_assign. assumption.

      destruct (simplify_exp _ e1) eqn: SE1.
      - right. einversion trivial IHe1. rewrite SE1. econstructor.
        subst. constructor.
      - right. einversion trivial SV. einversion trivial IHe1.
        rewrite SE1. constructor. eassumption. subst. constructor.
        assumption.
      - left. reflexivity.
    }

Unshelve. all: exact s0.
Qed.

Definition trace_states := option ((addr -> store_delta) * Prop * list addr).
Definition trace_state_res := option (list (store_delta * option exit)).
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

Lemma map_option_includes: forall A B (f: A -> option B) l l' a b
  (Maps: map_option f l = Some l') (F: f a = Some b) (InL: In a l),
  In b l'.
Proof.
Admitted.

Fixpoint simple_trace_stmt (δ: store_delta) (q: stmt): trace_state_res :=
  match q with
  | Nop => Some ((δ, None) :: nil)
  | Move v e => Some ((δ[v := simplify_exp δ e], None) :: nil)
  | Jmp e =>
      match simplify_exp δ e with
      | Number n _ => Some ((δ, Some (Exit n)) :: nil)
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


Theorem simple_trace_stmt_correct: forall c0 s0 q paths c c' h s s' x δ
  (MDL0: models c0 s0) (STyp: hastyp_stmt c0 c q c') (MDL: models c s)
  (DMDL: delta_models c0 c δ) (DS: delta_safety c0 δ) (HD: has_delta s0 s δ)
  (XS: exec_stmt h s q s' x) (STS: simple_trace_stmt δ q = Some paths),
  Exists (fun '(δ', x') => x' = x /\ has_delta s0 s' δ') paths.
Proof.
  induction q; intros; inversion XS; inversion STS; inversion STyp; subst;
  clear XS STS.
  - (* Nop *) constructor. split. reflexivity. assumption.
  - (* Move *) constructor. split. reflexivity. apply has_delta_assign.
    assumption. eassert (Safe: safety c0 _). apply safety_simplify_exp.
    eassumption. destruct simplify_exp eqn: SE.
    + right. einversion trivial eval_simple_exp_total.
      erewrite (simplify_exp_correct _ _ s0); try rewrite SE; try eassumption.
    + right. einversion trivial eval_simple_exp_total.
      erewrite (simplify_exp_correct _ _ s0); try rewrite SE; try eassumption.
    + left. assumption.
  - (* Jmp *) eassert (Safe: safety c0 _). apply safety_simplify_exp. eassumption.
    destruct simplify_exp eqn: SE; inversion H3; subst. constructor. split;
    try assumption. einversion trivial eval_simple_exp_total. rewrite SE. discriminate.
    erewrite <- (simplify_exp_correct _ _ s0) in H0 by eassumption.
    rewrite SE in H0. inversion H0. reflexivity.
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
    destruct (simple_trace_stmt δ1 q2) eqn:SQ2. einstantiate IHq2; try assumption;
    try apply SQ2; try apply TS2; try apply XS0. eapply preservation_exec_stmt;
    eassumption. all: admit.
  - (* If/else *) admit.
Admitted.

Definition get_reg v (ts: trace_state_res) :=
  match ts with
  | None => nil
  | Some (paths, _) => map (fun '(δ, _) => δ v) paths
  end.
Require Import strchr_i386.
Require Import fstat_i386.
Definition null_state: store := fun _ => VaN 0 0.

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
