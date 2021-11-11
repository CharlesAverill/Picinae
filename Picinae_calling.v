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

Inductive hastyp_simple_exp (c: typctx): simple_exp -> typ -> Prop :=
  | TSE_Num (n: N) (w: bitwidth) (LT: n < 2 ^ w):
      hastyp_simple_exp c (Number n w) (NumT w)
  | TSE_VarOff (v: var) (w: bitwidth) (off: N) (CV: c v = Some (NumT w))
      (LT: off < 2 ^ w): hastyp_simple_exp c (VarOff v off w) (NumT w).

Lemma hastyp_simple_exp_num:
  forall c e t (TSE: hastyp_simple_exp c e t), exists w, t = NumT w.
Proof.
  intros. inversion TSE; eexists; reflexivity.
Qed.

Lemma sexp_width_type_correct: forall c e w (TSE: hastyp_simple_exp c e (NumT w)),
  sexp_width e = Some w.
Proof.
  intros. inversion TSE; reflexivity.
Qed.

Fixpoint simplify_exp (c0: typctx) (δ: store_delta) e :=
  match e with
  | Var v => δ v
  | Word n w => Number n w
  | Load _ _ _ _ => Complex
  | Store _ _ _ _ _ => Complex
  | BinOp op e1 e2 =>
      let of_oper v offset n (is_inverted: bool) :=
        match c0 v with
        | Some (NumT w) =>
            match op with
            | OP_PLUS => if is_inverted then
                VarOff v ((n + offset) mod 2 ^ w) w
              else
                VarOff v ((offset + n) mod 2 ^ w) w
            | OP_MINUS => if is_inverted then Complex else
                VarOff v ((offset + 2 ^ w - n) mod 2 ^ w) w
            | _ => Complex
            end
        | None | Some (MemT _) => Complex
        end in
      match simplify_exp c0 δ e1, simplify_exp c0 δ e2 with
      | Complex, _ | _, Complex | VarOff _ _ _, VarOff _ _ _ => Complex
      | Number n1 w1, Number n2 w2 =>
          if w1 == w2 then
            match eval_binop op w1 n1 n2 with
            | VaN n w' => Number n w'
            | VaM _ _ => Complex
            end
          else Complex
      | VarOff v1 off1 w1, Number n2 w2 =>
          if w1 == w2 then of_oper v1 off1 n2 false
          else Complex
      | Number n1 w1, VarOff v2 off2 w2 =>
          if w1 == w2 then of_oper v2 off2 n1 true
          else Complex
      end
  | UnOp _ _ => Complex
  | Cast typ w' e =>
      let se := simplify_exp c0 δ e in
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
  | Let v e e_in =>
      simplify_exp c0 (update δ v (simplify_exp c0 δ e)) e_in
  | Unknown _ => Complex
  | Ite _ _ _ => Complex
  | Extract _ _ _ => Complex
  | Concat _ _ => Complex
  end.

Inductive eval_stack_exp (s: store): simple_exp -> value -> Prop :=
  | ESE_Number n w: eval_stack_exp s (Number n w) (VaN n w)
  | ESE_VarOff v n off w (SV: s v = VaN n w): eval_stack_exp s
      (VarOff v off w) (VaN ((n + off) mod 2 ^ w) w).

Lemma eval_stack_exp_num: forall s se v (ESE: eval_stack_exp s se v),
  exists n w, v = VaN n w.
Proof.
  intros. inversion ESE; subst; clear ESE; eexists; eexists; reflexivity.
Qed.

Definition has_delta (s s': store) (δ: store_delta) :=
  forall v val (ESE: eval_stack_exp s (δ v) val), s' v = val.

Definition delta_safety (c0: typctx) (δ: store_delta) :=
  forall v0 v off w (EQ_V: (δ v) = VarOff v0 off w), c0 v0 = Some (NumT w).

Definition delta_models (c: typctx) (δ: store_delta) :=
  forall v t (CV: c v = Some t), hastyp_simple_exp c (δ v) t.

(*
Theorem stack_equiv_imp_models: forall c s st
  (MDL: models c s) (SEQ: stack_equiv s st), stack_models c st.
Proof.
  unfold stack_models. intros.
  specialize (MDL _ _ CV) as MDL_V. inversion MDL_V. subst. clear MDL_V.
  specialize (MDL _ _ C_SP). inversion MDL. subst. clear MDL.
  destruct (st v) eqn: ST; inversion SEW; subst; clear SEW.
  - (* Imm *) erewrite SEQ in H0; [|rewrite ST; constructor]. inversion H0.
    reflexivity.
  - (* VarOff *) erewrite SEQ in H0; [|rewrite ST; constructor;
    symmetry; eassumption]. inversion H0. reflexivity.
Qed.

Theorem preservation_simplify_exp0: forall e w w' c st
  (ETyp: hastyp_exp c e (NumT w)) (SMDL: stack_models c st)
  (ESBits: Some w' = sexp_width (simplify_exp0 st e))
  (C_SP: c sp_reg = Some (NumT reg_bitwidth)), w = w'.
Proof.
  intros.
  (* assert SP < 2 ^ reg_bitwidth *)
  revert e st c w w' C_SP SMDL ETyp ESBits.
  induction e; intros; try discriminate.
  - (* Var *) simpl in ESBits. inversion ETyp. subst. eapply SMDL; eassumption.
  - (* Word *) inversion ESBits. inversion ETyp. reflexivity.
  - (* Binop *) inversion ETyp. subst. clear ETyp. simpl in ESBits.
    specialize (IHe1 st). specialize (IHe2 st).
    destruct (simplify_exp0 _ e1) eqn: C1; try discriminate;
    destruct (simplify_exp0 _ e2) eqn: C2; try discriminate;
    destruct (_ == _) eqn: EQB; try discriminate;
    destruct b; try solve
      [ discriminate
      | inversion ESBits; reflexivity
      | (eapply IHe1 + eapply IHe2); eassumption ].
  - (* Cast *) inversion ETyp. subst. clear ETyp. simpl in ESBits.
    specialize (IHe st). destruct (sexp_width _) eqn: SEW; try discriminate.
    replace b with w1; [| eapply IHe; solve [eassumption|reflexivity]].
    destruct (simplify_exp0 _ _) eqn: C1; try discriminate.

    (* Imm *)
    inversion ESBits. reflexivity.

    (* VarOff *)
    inversion SEW. subst. clear SEW. assert (w1 = reg_bitwidth);
      [eapply IHe; solve [eassumption|reflexivity]|subst].
    destruct c; destruct (_ <=? _) eqn: LEB; try discriminate;
    apply N.leb_le in LEB; inversion ESBits; subst; clear ESBits;
    apply N.le_antisymm;eassumption.
  - (* Let *) inversion ETyp. subst. simpl in ESBits.
    destruct (sp_reg == v); try discriminate.
    eapply (IHe2 (fun v' => if v' == v then _ else _) (c[_ := _])); try eassumption.

    (* C_SP' *) rewrite update_frame by assumption. assumption.

    (* SMDL' *) unfold stack_models. intros. { destruct (v0 == v).
      - subst. eapply IHe1; try eassumption.
        rewrite update_updated in CV. inversion CV.
        subst. clear CV. assumption.
      - subst. rewrite update_frame in CV by assumption. eapply SMDL; eassumption.
    }
Qed.
*)

Theorem preservation_simplify_exp: forall e t c δ
  (ETyp: hastyp_exp c e t) (DMDL: delta_models c δ),
  hastyp_simple_exp c (simplify_exp c δ e) t.
Proof.
Admitted.

Corollary preservation_bitwidth_simplify_exp: forall e c δ w
  (TE: hastyp_exp c e (NumT w)) (DMDL: delta_models c δ),
  sexp_width (simplify_exp c δ e) = Some w.
Proof.
  intros. eapply sexp_width_type_correct. eapply preservation_simplify_exp;
  eassumption.
Qed.

Theorem simplify_exp_correct: forall e h s0 s δ vs ve c t
  (ETyp: hastyp_exp c e t) (MDL0: models c s0) (MDL: models c s)
  (DS: delta_safety c δ) (DMDL: delta_models c δ) (HD: has_delta s0 s δ)
  (EE: eval_exp h s e ve) (ESE: eval_stack_exp s0 (simplify_exp c δ e) vs), ve = vs.
Proof.
  intros.

  (* Specify vs *)
  apply eval_stack_exp_num in ESE as VS. destruct VS as [n' [w' VS]]. subst.

  (*
  assert (SMDL: stack_models c st). eapply stack_equiv_imp_models; eassumption.
  (* assert SP < 2 ^ reg_bitwidth *)
  specialize (MDL sp_reg _ SP_Reg) as MDL_SP. inversion MDL_SP. subst.
  symmetry in H0. clear MDL_SP.
   *)
  revert c s δ n' w' ve t MDL0 MDL DMDL DS HD ETyp EE ESE.
  induction e; intros; try solve [inversion ESE].
  - (* Var *) inversion EE. subst. eapply HD. eassumption.
  - (* Word *) inversion EE. inversion ESE. subst. reflexivity.
  - (* BinOp *) inversion EE. inversion ETyp. subst. clear EE ETyp.

    (* Clean up some of the bitwidth variables, to ensure w = w0 *)
    eassert (TV1: hastyp_val _ _). eapply (preservation_eval_exp MDL T1);
      eassumption.
    eassert (TV2: hastyp_val _ _). eapply (preservation_eval_exp MDL T2);
      eassumption.
    eassert (TSE1: hastyp_simple_exp _ (simplify_exp _ _ e1) _).
      eapply preservation_simplify_exp; eassumption.
    eassert (TSE2: hastyp_simple_exp _ (simplify_exp _ _ e2) _).
      eapply preservation_simplify_exp; eassumption.
    inversion TV1. inversion TV2. subst. clear TV1 TV2 H5.

    (* This is a common assumption that we will have to make *)
    assert (2 ^ w0 <> 0). destruct w0; discriminate.

    (* Do a bunch of case destructions *)
    simpl in ESE. destruct (simplify_exp _ _ e1) eqn: C1; try solve [inversion ESE];
    destruct (simplify_exp _ _ e2) eqn: C2; try solve [inversion ESE];
    destruct (w == _) eqn: EQW; try solve [inversion ESE];
    try destruct (c v) eqn: CV; try solve [inversion ESE];
    try destruct t; try solve [inversion ESE];
    inversion TSE1; inversion TSE2; subst;
    destruct b; simpl in ESE; inversion ESE; subst; clear ESE;
    try (rewrite CV0 in CV; inversion CV; subst; clear CV);

    (* Push indutive hypothesis*)
    (eassert (Equiv1: VaN n1 _ = VaN _ _); [
      eapply IHe1; solve [eassumption|rewrite C1; econstructor; eassumption]
    |]); inversion Equiv1; subst; clear Equiv1;
    (eassert (Equiv2: VaN n2 _ = VaN _ _); [
      eapply IHe2; solve [eassumption|rewrite C2; econstructor; eassumption]
    |]); inversion Equiv2; subst; clear Equiv2;

    (* Trivial cases for imm OP imm *)
    try reflexivity;

    (* Next we need to extract condition for register to be smaller than 2 ^ w' *)
    (eassert (TV: hastyp_val _ _); [eapply MDL0; eassumption|
    inversion TV; rewrite SV in H1; inversion H1; subst; clear TV H1; simpl]).

      (* imm + var *)
      erewrite <- (N.mod_small n) at 1 by eassumption.
      erewrite <- (N.mod_small n0) at -1; [|eassumption].
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
  - (* Cast *) inversion EE. inversion ETyp. subst.
    specialize (preservation_eval_exp MDL T1 E1) as TV. inversion TV. subst.

    (* sexp_width _ = Some w1 *)
    clear EE ETyp TV. simpl in ESE. destruct (sexp_width _) eqn: EQW;
      try solve [inversion ESE]. symmetry in EQW.
    assert (w1 = b). eapply preservation_simplify_exp0; eassumption. subst.

    (* Speciailize IH *)
    assert (IHe2: forall ve vs, eval_exp h s e ve ->
      eval_stack_exp s (simplify_exp0 st e) vs -> ve = vs).
    intros. eapply IHe; eassumption.

    destruct (simplify_exp0 _ e) eqn: C'; try solve [inversion ESE].

    (* For Imm *)
    inversion ESE. subst. clear ESE. f_equal. f_equal.
    assert (Equiv1: VaN n0 b = VaN n1 w0). eapply IHe2;
    try solve [eassumption|constructor]. inversion Equiv1. reflexivity.

    (* For VarOff *)
    destruct c; destruct (_ <=? _) eqn: LEB; try solve [inversion ESE];
    apply N.leb_le in LEB; (assert (w = b); [apply N.le_antisymm;
    eassumption|subst]).
    + (* CAST_LOW *) simpl. rewrite N.mod_small; [|assumption]. eapply IHe2;
      eassumption.
    + (* CAST_HIGH *) simpl. rewrite N.sub_diag. simpl. eapply IHe2;
      eassumption.
    + (* CAST_SIGNED *) simpl. unfold scast. rewrite ofZ_toZ, N.mod_small;
      [|assumption]. eapply IHe2; eassumption.
    + (* CAST_UNSIGNED *) simpl. eapply IHe2; try eassumption.
  - (* Let *) inversion EE. inversion ETyp. subst. clear EE ETyp.
    simpl in ESE. destruct (sp_reg == v). inversion ESE.
    eassert (ESE': eval_stack_exp (s[_ := _]) (simplify_exp0 _ e2) vs). {
      destruct (simplify_exp0 _ e2) eqn: C2; rewrite C2; inversion ESE; subst.
      - constructor.
      - constructor. rewrite update_frame. assumption. eassumption.
    }
    eapply (IHe2 (c[_ := _]) (s[_ := _])); try eassumption; clear ESE'.

    (* S_SP' *) rewrite update_frame by assumption. assumption.
    (* SMDL' *) unfold stack_models. intros. { destruct (v0 == v).
      - subst. rewrite update_updated in CV. inversion CV.
        subst. clear CV. eapply preservation_simplify_exp0; eassumption.
      - subst. rewrite update_frame in CV by assumption. eapply SMDL; eassumption.
    }
    (* MDL *) unfold models. intros. { destruct (v0 == v).
      - subst. rewrite update_updated in CV. inversion CV. subst. clear CV.
        rewrite update_updated. eapply preservation_eval_exp; eassumption.
      - subst. rewrite update_frame in CV by assumption.
        rewrite update_frame by assumption. apply MDL; assumption.
    }
    (* SP_REG' *) rewrite update_frame by assumption. assumption.
    (* SEQ' *) unfold stack_equiv. intros v0 val ESE1. { destruct (v0 == v).
      - subst. rewrite update_updated. eapply IHe1; try eassumption.
        destruct (simplify_exp0 _ e1) eqn: C1; inversion ESE1; subst.
        + constructor.
        + constructor. rewrite update_frame in S_SP by assumption. assumption.
      - rewrite update_frame by assumption. eapply SEQ.
        destruct (st v0) eqn: CS; inversion ESE1; subst.
        + constructor.
        + constructor. rewrite update_frame in S_SP by assumption. assumption.
    }
Qed.

Theorem simplify_exp_red: forall e h s vs ve c t
  (ETyp: hastyp_exp c e t) (MDL: models c s)
  (EE: eval_exp h s e ve) (ESE: eval_stack_exp s (simplify_exp e) vs)
  (SP_Reg: c sp_reg = Some (NumT reg_bitwidth)), ve = vs.
Proof.
  intros. eapply simplify_exp0_red; try eassumption.
  unfold stack_equiv. intros v0 val ESE1.
  destruct (sp_reg == v0); inversion ESE1; subst; clear ESE1.
  rewrite S_SP. f_equal. rewrite N.add_0_r, N.mod_small. reflexivity.
  specialize (MDL _ _ SP_Reg). inversion MDL. subst. rewrite <- H0 in S_SP.
  inversion S_SP. subst. assumption.
Qed.

Inductive stack_oper :=
  | SPOper (must_fall: bool) (off: N)
  | OtherOper (must_fall: bool)
  | ErrorOper.

Definition check_fallthru must_fall (x: option exit) :=
  must_fall = false \/ x = None.

Inductive exec_stack_oper (s: store):
  store -> (option exit -> Prop) -> stack_oper -> Prop :=
  | ESO_UpdateSP e off v must_fall (ESE: eval_stack_exp s e v)
      (E_VarOff: e = VarOff off): exec_stack_oper s (s[sp_reg := v])
      (check_fallthru must_fall) (SPOper must_fall off)
  | ESO_OtherOper must_fall: exec_stack_oper s s
      (check_fallthru must_fall) (OtherOper must_fall).

(* Classifies a statement by what it does to the stack. *)
Fixpoint simplify_stmt (q: stmt): stack_oper :=
  match q with
  | Nop => OtherOper true
  | Move v e =>
      if sp_reg == v then
        match simplify_exp e with
        | Imm _ _ => ErrorOper
        | VarOff off => SPOper true off
        | Complex => ErrorOper
        end
      else OtherOper true
  | Jmp _ => OtherOper false
  | Exn _ => OtherOper false
  | Seq q1 q2 =>
      match simplify_stmt q1, simplify_stmt q2 with
      | OtherOper true, x | x, OtherOper true => x
      | SPOper true off, OtherOper false => SPOper false off
      | SPOper true off1, SPOper true off2 => SPOper true (off1 + off2)
      | OtherOper false, OtherOper false => OtherOper false
      | _, _ => ErrorOper
      end
  | If _ q1 q2 =>
      match simplify_stmt q1, simplify_stmt q2 with
      | OtherOper falls, OtherOper falls2 =>
          OtherOper (falls && falls2)%bool
      | _, _ => ErrorOper
      end
  | Rep _ s =>
      match simplify_stmt s with
      | OtherOper falls => OtherOper falls
      | _ => ErrorOper
      end
  end.

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
  - (* Seq *) inversion XS; subst; destruct (simplify_stmt q1) eqn: C1;
    destruct (simplify_stmt q2) eqn: C2; try constructor; inversion XS; subst;
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
    destruct (simplify_stmt q1) eqn: C1; destruct (simplify_stmt q2) eqn: C2;
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

Fixpoint addrs (x:nat) :=
  match x with
  | O => 0 :: nil
  | S x' => N.of_nat x :: addrs x'
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
