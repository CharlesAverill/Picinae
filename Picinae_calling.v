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

Definition set A := list A.
Definition eqb {A} {eq: EqDec A} (a b: A): bool :=
  if a == b then true else false.
Arguments eqb {A} {eq} (a b): simpl never.
Definition set_elems {A} (s: set A): list A := s.
Definition set_exists {A} {e: EqDec A} (s: set A) (a: A): bool :=
  existsb (eqb a) s.
Definition set_nil {A}: set A := nil.
Definition set_add {A} {e: EqDec A} (s: set A) (a: A): set A :=
  if set_exists s a then s else a :: s.
Definition set_ap {A} {e: EqDec A} (s1 s2: set A): set A :=
  filter (fun a => negb (set_exists s2 a)) s1 ++ s2.

Theorem eqb_refl: forall A {e: EqDec A} (a: A), eqb a a = true.
Proof.
  intros. unfold eqb.
  destruct (a == a); [reflexivity|].
  destruct n. reflexivity.
Qed.

Theorem eqb_eq: forall A {e: EqDec A} (a a': A), a = a' <-> eqb a a' = true.
Proof.
  intros. unfold eqb.
  destruct (a == a'). split; intro; [reflexivity|assumption].
  split; intro; [destruct n; assumption|discriminate].
Qed.

Theorem eqb_neq: forall A {e: EqDec A} (a a': A), a <> a' <-> eqb a a' = false.
Proof.
  intros. unfold eqb.
  destruct (a == a'). split; intro; [destruct H; assumption|discriminate].
  split; intro; [reflexivity|assumption].
Qed.

Theorem set_ex_add_frame: forall A {e: EqDec A} (s: set A) (a a': A)
  (NE: a' <> a), set_exists (set_add s a) a' = set_exists s a'.
Proof.
  intros. unfold set_add, set_exists.
  destruct (existsb _ s) eqn: EX; [reflexivity|]. simpl.
  rewrite (proj1 (eqb_neq _ _ _) NE). reflexivity.
Qed.

Theorem set_ex_add_this: forall A {e: EqDec A} (s: set A) (a: A),
  set_exists (set_add s a) a = true.
Proof.
  intros. unfold set_add, set_exists.
  destruct (existsb _ s) eqn: EX; [assumption|]. simpl. rewrite eqb_refl.
  reflexivity.
Qed.

Theorem set_ex_ap_orb: forall A {e: EqDec A} (s1 s2: set A) (a: A),
  set_exists (set_ap s1 s2) a = set_exists s1 a || set_exists s2 a.
Proof.
  intros. unfold set_ap, set_exists.

  (* Found in s2 *)
  destruct (existsb _ s2) eqn: EX2. rewrite existsb_app, EX2, orb_true_r,
  Bool.orb_true_r. reflexivity.

  (* Not in s2... *)
  rewrite existsb_app, EX2, orb_false_r, orb_false_r.

  (* ... but in s1 *)
  destruct (existsb _ s1) eqn: EX1. apply existsb_exists. eexists.
  apply existsb_exists in EX1. destruct EX1 as [a' [In Eq]].
  apply eqb_eq in Eq. subst. split; [|apply eqb_refl]. apply filter_In.
  split; [assumption|]. rewrite EX2. reflexivity.

  (* ... or not in either *)
  destruct (existsb _ (filter _ _)) eqn: EX12; [|reflexivity].
  apply existsb_exists in EX12. destruct EX12 as [a' [In Eq]].
  apply eqb_eq in Eq. subst. apply filter_In in In. destruct In as [InS1 _].
  symmetry. rewrite <- EX1. apply existsb_exists. eexists.
  split; [eassumption|apply eqb_refl].
Qed.

Corollary set_ex_ap_or: forall A {e: EqDec A} (s1 s2: set A) (a: A),
  set_exists s1 a = true \/ set_exists s2 a = true ->
  set_exists (set_ap s1 s2) a = true.
Proof.
  intros. rewrite set_ex_ap_orb. apply orb_true_intro. assumption.
Qed.

Corollary set_ex_ap_l: forall A {e: EqDec A} (s1 s2: set A) (a: A)
  (EX1: set_exists s1 a = true), set_exists (set_ap s1 s2) a = true.
Proof. intros. apply set_ex_ap_or. left. assumption. Qed.

Corollary set_ex_ap_r: forall A {e: EqDec A} (s1 s2: set A) (a: A)
  (EX2: set_exists s2 a = true), set_exists (set_ap s1 s2) a = true.
Proof. intros. apply set_ex_ap_or. right. assumption. Qed.

(* partial functions *)
Definition pfunc (A B:Type) := A -> option B.
Bind Scope pfunc_scope with pfunc.
Open Scope pfunc_scope.
Notation "x ⇀ y" := (pfunc x y) (at level 99, y at level 200, right associativity): type_scope.

(* the empty function (bottom) *)
Notation "⊥" := (fun _ => None).

(* composition of partial functions *)
Definition pcompose {A:Type} (f g : A ⇀ A) (x : A) :=
  match g x with None => None | Some y => f y end.
Notation "f ○ g" := (pcompose f g) (at level 40, g at next level, left associativity) : pfunc_scope.

Definition pupdate {A B} {e: EqDec A} (s: A ⇀ B) (key: A) (val: B): pfunc A B :=
  fun key' => if key' == key then Some val else s key'.

Definition premove {A B} {e: EqDec A} (s: A ⇀ B) (key: A): pfunc A B :=
  fun key' => if key' == key then None else s key'.

Theorem pupdate_frame: forall A B {e: EqDec A} (s: pfunc A B) (key key': A) val
  (NE: key' ≠ key), (pupdate s key val) key' = s key'.
Proof.
  intros. unfold pupdate. destruct (key' == key); [|reflexivity]. destruct NE.
  assumption.
Qed.

Theorem premove_frame: forall A B {e: EqDec A} (s: pfunc A B) (key key': A)
  (NE: key' ≠ key), (premove s key) key' = s key'.
Proof.
  intros. unfold premove. destruct (key' == key); [|reflexivity]. destruct NE.
  assumption.
Qed.

Theorem pupdate_this: forall A B {e: EqDec A} (s: pfunc A B) (key: A) val,
  (pupdate s key val) key = Some val.
Proof.
  intros. unfold pupdate. destruct (iseq_refl key). rewrite H. reflexivity.
Qed.

Theorem premove_this: forall A B {e: EqDec A} (s: pfunc A B) (key: A),
  (premove s key) key = None.
Proof.
  intros. unfold premove. destruct (iseq_refl key). rewrite H. reflexivity.
Qed.

Fixpoint get_jumps (s: stmt): option (set addr) :=
  match s with
  | Nop => Some set_nil
  | Move _ _ => Some set_nil
  | Jmp e =>
      match e with
      | Word loc _ => Some (set_add set_nil loc)
      | _ => None
      end
  | Exn _ => Some set_nil
  | Seq s1 s2 | If _ s1 s2 =>
      match (get_jumps s1, get_jumps s2) with
      | (_, None) => None
      | (None, _) => None
      | (Some j1, Some j2) => Some (set_ap j1 j2)
      end
  | Rep _ s => get_jumps s
  end.

Lemma jump_rep_total: forall e q h s s' x a
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

Theorem get_jumps_complete: forall q h s0 s1 x a' jmps
  (XS: exec_stmt h s0 q s1 x) (EX: x = Some (Exit a'))
  (JMPS: Some jmps = get_jumps q), set_exists jmps a' = true.
Proof.
  induction q; intros; inversion XS; subst; simpl in *; try discriminate.
  - (* Jmp *) inversion E; subst; simpl in *; clear E; try discriminate.
    inversion H2. subst. inversion JMPS. apply set_ex_add_this.
  - (* Seq, exit in q1 *) destruct (get_jumps q1) eqn: J1;
    destruct (get_jumps q2) eqn: J2; try discriminate. inversion JMPS. subst.
    clear JMPS. apply set_ex_ap_l. eapply IHq1. eassumption. assumption. reflexivity.
  - (* Seq, exit in q2 *) destruct (get_jumps q1) eqn: J1;
    destruct (get_jumps q2) eqn: J2; try discriminate. inversion JMPS. subst.
    clear JMPS. apply set_ex_ap_r. eapply IHq2. eassumption. reflexivity. reflexivity.
  - (* If *) destruct (get_jumps q1) eqn: J1; destruct (get_jumps q2) eqn: J2;
    try discriminate. inversion JMPS. subst. clear JMPS. apply set_ex_ap_or.
    destruct c; [right; eapply IHq2|left; eapply IHq1];
        try solve [eassumption|reflexivity].
  - (* Evil rep *) destruct (jump_rep_total _ _ _ _ _ _ _ XS eq_refl) as
    [s2 [s3 SInner]]. eapply IHq; solve [reflexivity|eassumption].
Qed.

Parameter sp_reg: var
(* Definition sp_reg := R_ESP*).

Parameter reg_bitwidth: bitwidth
(* Definition reg_bitwidth: bitwidth := 32. *).

Inductive stack_exp :=
  | Imm (w: bitwidth) (n: N)
  | SPOff (off: N)
  | UnkVal.

Definition sexp_width (e: stack_exp) :=
  match e with
  | Imm w _ => Some w
  | SPOff _ => Some reg_bitwidth
  | UnkVal => None
  end.

Fixpoint classify_exp0 st e :=
  match e with
  | Var v => st v
  | Word n w => Imm w n
  | Load _ _ _ _ => UnkVal
  | Store _ _ _ _ _ => UnkVal
  | BinOp op e1 e2 =>
      let of_oper sp_off n (is_inverted: bool) :=
        match op with
        | OP_PLUS => if is_inverted then
            SPOff ((n + sp_off) mod 2 ^ reg_bitwidth)
          else
            SPOff ((sp_off + n) mod 2 ^ reg_bitwidth)
        | OP_MINUS => if is_inverted then UnkVal else
            SPOff ((sp_off + 2 ^ reg_bitwidth - n) mod 2 ^ reg_bitwidth)
        | _ => UnkVal
        end in
      match classify_exp0 st e1, classify_exp0 st e2 with
      | UnkVal, _ | _, UnkVal | SPOff _, SPOff _ => UnkVal
      | Imm w1 n1, Imm w2 n2 =>
          if w1 == w2 then
            match eval_binop op w1 n1 n2 with
            | VaN n w' => Imm w' n
            | VaM _ _ => UnkVal
            end
          else UnkVal
      | SPOff off1, Imm w2 n2 =>
          if w2 == reg_bitwidth then of_oper off1 n2 false
          else UnkVal
      | Imm w1 n1, SPOff off2 =>
          if w1 == reg_bitwidth then of_oper off2 n1 true
          else UnkVal
      end
  | UnOp _ _ => UnkVal
  | Cast typ w' e =>
      let se := classify_exp0 st e in
      match sexp_width se with
      | Some w =>
          match se with
          | Imm _ n => Imm w' (cast typ w w' n)
          | SPOff _ =>
              match typ with
              | CAST_LOW | CAST_HIGH => (* narrowing *)
                  if w <=? w' then se else UnkVal
              | CAST_UNSIGNED | CAST_SIGNED => (* widening *)
                  if w' <=? w then se else UnkVal
              end
          | UnkVal => UnkVal
          end
      | None => UnkVal
      end
  | Let v e e_in =>
      if sp_reg == v then UnkVal
      else classify_exp0 (fun v' =>
        if v' == v then classify_exp0 st e else st v') e_in
  | Unknown _ => UnkVal
  | Ite _ _ _ => UnkVal
  | Extract _ _ _ => UnkVal
  | Concat _ _ => UnkVal
  end.

Definition classify_exp (e: exp): stack_exp :=
   classify_exp0 (fun v' => if sp_reg == v' then SPOff 0 else UnkVal) e.

Inductive eval_stack_exp (s: store): stack_exp -> value -> Prop :=
  | ESE_Imm w n: eval_stack_exp s (Imm w n) (VaN n w)
  | ESE_SPOff sp off (S_SP: s sp_reg = VaN sp reg_bitwidth):
      eval_stack_exp s (SPOff off) (VaN ((sp + off) mod 2 ^ reg_bitwidth) reg_bitwidth).

Definition stack_equiv (s: store) (st: var → stack_exp) :=
  forall var val, eval_stack_exp s (st var) val -> s var = val.

Definition stack_models (c: typctx) (st: var → stack_exp) :=
  forall v b b' (CV: c v = Some (NumT b)) (SEW: Some b' = sexp_width (st v)),
  b = b'.

Theorem stack_equiv_imp_models: forall c s st
  (C_SP: c sp_reg = Some (NumT reg_bitwidth)) (MDL: models c s)
  (SEQ: stack_equiv s st), stack_models c st.
Proof.
  unfold stack_models. intros.
  specialize (MDL _ _ CV) as MDL_V. inversion MDL_V. subst. clear MDL_V.
  specialize (MDL _ _ C_SP). inversion MDL. subst. clear MDL.
  destruct (st v) eqn: ST; inversion SEW; subst; clear SEW.
  - (* Imm *) erewrite SEQ in H0; [|rewrite ST; constructor]. inversion H0.
    reflexivity.
  - (* SPOff *) erewrite SEQ in H0; [|rewrite ST; constructor;
    symmetry; eassumption]. inversion H0. reflexivity.
Qed.

Theorem preservation_classify_exp0: forall e w w' c st
  (ETyp: hastyp_exp c e (NumT w)) (SMDL: stack_models c st)
  (ESBits: Some w' = sexp_width (classify_exp0 st e))
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
    destruct (classify_exp0 _ e1) eqn: C1; try discriminate;
    destruct (classify_exp0 _ e2) eqn: C2; try discriminate;
    destruct (_ == _) eqn: EQB; try discriminate;
    destruct b; try solve
      [ discriminate
      | inversion ESBits; reflexivity
      | (eapply IHe1 + eapply IHe2); eassumption ].
  - (* Cast *) inversion ETyp. subst. clear ETyp. simpl in ESBits.
    specialize (IHe st). destruct (sexp_width _) eqn: SEW; try discriminate.
    replace b with w1; [| eapply IHe; solve [eassumption|reflexivity]].
    destruct (classify_exp0 _ _) eqn: C1; try discriminate.

    (* Imm *)
    inversion ESBits. reflexivity.

    (* SPOff *)
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

Theorem classify_exp0_red: forall e h s vs ve c t st
  (ETyp: hastyp_exp c e t) (MDL: models c s) (SEQ: stack_equiv s st)
  (EE: eval_exp h s e ve) (ESE: eval_stack_exp s (classify_exp0 st e) vs)
  (SP_Reg: c sp_reg = Some (NumT reg_bitwidth)), ve = vs.
Proof.
  intros.
  assert (SMDL: stack_models c st). eapply stack_equiv_imp_models; eassumption.
  (* assert SP < 2 ^ reg_bitwidth *)
  specialize (MDL sp_reg _ SP_Reg) as MDL_SP. inversion MDL_SP. subst.
  symmetry in H0. clear MDL_SP.
  revert c s st n LT H0 vs ve t SMDL MDL ETyp SP_Reg SEQ EE ESE.
  induction e; intros; try solve [inversion ESE].
  - (* Var *) inversion EE. subst. apply SEQ. assumption.
  - (* Word *) inversion EE. inversion ESE. subst. reflexivity.
  - (* BinOp *) inversion EE. inversion ETyp. subst. clear EE ETyp.
    assert (2 ^ reg_bitwidth <> 0). destruct reg_bitwidth; discriminate.
    simpl in ESE. destruct (classify_exp0 _ e1) eqn: C1; try solve [inversion ESE];
    destruct (classify_exp0 _ e2) eqn: C2; try solve [inversion ESE];
    destruct (w1 == _) eqn: EQW; try solve [inversion ESE];
    (* Push the inductive hypothesis *)
    (eassert (Equiv1: VaN n1 w = VaN _ _);[eapply IHe1;
      solve [eassumption|rewrite C1; econstructor; eassumption] |] );
    (eassert (Equiv2: VaN n2 w = VaN _ _);[eapply IHe2;
      solve [eassumption|rewrite C2; econstructor; eassumption] |] );
    inversion Equiv1; inversion Equiv2; subst; clear IHe1 IHe2 Equiv1 Equiv2.
    + (* imm OP imm *) destruct (eval_binop _ _ n0 n3) eqn: Ev; [|inversion ESE].
      inversion ESE. subst. clear ESE. rewrite <- Ev. reflexivity.
    + (* imm OP SP *) destruct b; inversion ESE; subst; clear ESE. simpl.
      specialize (preservation_eval_exp MDL T1 E1) as TV. inversion TV. subst.
      rewrite H0 in S_SP. inversion S_SP. subst.
      erewrite <- (N.mod_small n0) at 1; [|eassumption].
      erewrite <- (N.mod_small sp) at -1; [|eassumption].
      repeat rewrite <- N.add_mod by assumption. f_equal. f_equal.
      rewrite N.add_assoc, (N.add_comm n0), <- N.add_assoc. reflexivity.
    + (* SP OP imm *) destruct b; inversion ESE; subst; clear ESE;
      specialize (preservation_eval_exp MDL T2 E2) as TV; inversion TV; subst;
      rewrite H0 in S_SP; inversion S_SP; subst.
      (* OP_PLUS *) simpl. erewrite <- (N.mod_small n0) at 1; [|eassumption].
      erewrite <- (N.mod_small sp) at -1; [|eassumption].
      repeat rewrite <- N.add_mod by assumption. f_equal. f_equal.
      rewrite N.add_assoc. reflexivity.
      (* OP_MINUS *) unfold eval_binop, towidth. rewrite N.add_comm. f_equal.
      apply N.lt_le_incl in LT0. rewrite <- N.add_sub_assoc, <- N.add_sub_assoc,
        N.add_mod, N.mod_mod, <- N.add_mod, (N.add_mod sp), N.mod_mod,
      <- N.add_mod, N.add_assoc by assumption. reflexivity.
  - (* Cast *) inversion EE. inversion ETyp. subst.
    specialize (preservation_eval_exp MDL T1 E1) as TV. inversion TV. subst.

    (* sexp_width _ = Some w1 *)
    clear EE ETyp TV. simpl in ESE. destruct (sexp_width _) eqn: EQW;
      try solve [inversion ESE]. symmetry in EQW.
    assert (w1 = b). eapply preservation_classify_exp0; eassumption. subst.

    (* Speciailize IH *)
    assert (IHe2: forall ve vs, eval_exp h s e ve ->
      eval_stack_exp s (classify_exp0 st e) vs -> ve = vs).
    intros. eapply IHe; eassumption.

    destruct (classify_exp0 _ e) eqn: C'; try solve [inversion ESE].

    (* For Imm *)
    inversion ESE. subst. clear ESE. f_equal. f_equal.
    assert (Equiv1: VaN n0 b = VaN n1 w0). eapply IHe2;
    try solve [eassumption|constructor]. inversion Equiv1. reflexivity.

    (* For SPOff *)
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
    eassert (ESE': eval_stack_exp (s[_ := _]) (classify_exp0 _ e2) vs). {
      destruct (classify_exp0 _ e2) eqn: C2; rewrite C2; inversion ESE; subst.
      - constructor.
      - constructor. rewrite update_frame. assumption. eassumption.
    }
    eapply (IHe2 (c[_ := _]) (s[_ := _])); try eassumption; clear ESE'.

    (* S_SP' *) rewrite update_frame by assumption. assumption.
    (* SMDL' *) unfold stack_models. intros. { destruct (v0 == v).
      - subst. rewrite update_updated in CV. inversion CV.
        subst. clear CV. eapply preservation_classify_exp0; eassumption.
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
        destruct (classify_exp0 _ e1) eqn: C1; inversion ESE1; subst.
        + constructor.
        + constructor. rewrite update_frame in S_SP by assumption. assumption.
      - rewrite update_frame by assumption. eapply SEQ.
        destruct (st v0) eqn: CS; inversion ESE1; subst.
        + constructor.
        + constructor. rewrite update_frame in S_SP by assumption. assumption.
    }
Qed.

Theorem classify_exp_red: forall e h s vs ve c t
  (ETyp: hastyp_exp c e t) (MDL: models c s)
  (EE: eval_exp h s e ve) (ESE: eval_stack_exp s (classify_exp e) vs)
  (SP_Reg: c sp_reg = Some (NumT reg_bitwidth)), ve = vs.
Proof.
  intros. eapply classify_exp0_red; try eassumption.
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
  (option exit -> Prop) -> stack_oper -> Prop :=
  | ESO_UpdateSP s' e off v must_fall (ESE: eval_stack_exp s e v)
      (E_SPOff: e = SPOff off): exec_stack_oper s (s[sp_reg := v])
      (check_fallthru must_fall) (SPOper must_fall off)
  | ESO_OtherOper must_fall: exec_stack_oper s s
      (check_fallthru must_fall) (OtherOper must_fall).

(* Classifies a statement by what it does to the stack. *)
Fixpoint classify_stmt (q: stmt): stack_oper :=
  match q with
  | Nop => OtherOper true
  | Move v e =>
      if sp_reg == v then
        match classify_exp e with
        | Imm _ _ => ErrorOper
        | SPOff off => SPOper true off
        | UnkVal => ErrorOper
        end
      else OtherOper true
  | Jmp _ => OtherOper false
  | Exn _ => OtherOper false
  | Seq q1 q2 =>
      match classify_stmt q1, classify_stmt q2 with
      | OtherOper true, x | x, OtherOper true => x
      | SPOper true off, OtherOper false => SPOper false off
      | SPOper true off1, SPOper true off2 => SPOper true (off1 + off2)
      | OtherOper false, OtherOper false => OtherOper false
      | _, _ => ErrorOper
      end
  | If _ q1 q2 =>
      match classify_stmt q1, classify_stmt q2 with
      | OtherOper falls, OtherOper falls2 =>
          OtherOper (falls && falls2)%bool
      | _, _ => ErrorOper
      end
  | Rep _ s =>
      match classify_stmt s with
      | OtherOper falls => OtherOper falls
      | _ => ErrorOper
      end
  end.

(*
Lemma classify_rep_stmt_red: forall q e h s s' x
  (EX: exec_stmt h s (Rep e q) s' x)
  (IHq : ∀ (s s' : store) (x : option exit) (EX : exec_stmt h s q s' x),
        exec_stack_oper h s q s' x EX (classify_stmt q)),
  match classify_stmt q with
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
  - (* n = 0 *) inversion XS. subst. clear XS. destruct classify_stmt;
    constructor; reflexivity.
  - (* n > 0 *) inversion XS; subst; clear XS.

    (* Terminated loop at this step *)
    specialize (IHq _ _ _ XS0).
    destruct classify_stmt; try solve [constructor]; inversion IHq.
    discriminate. assumption.

    (* Continue onwards in the loop *)
    specialize (IHq _ _ _ XS1).
    specialize (IHnn _ _ _ XS0).
    destruct classify_stmt; try solve [constructor]; inversion IHq.

    destruct IHnn. split. assumption.
    all: eapply eq_trans; eassumption.
Qed.
*)
Ltac fallthrus :=
  (left + right); reflexivity.

Theorem classify_stmt_red_sp: forall q h s s' s1' x c0 c1 c' Xcond
  (XS: exec_stmt h s q s' x) (ESO: exec_stack_oper s s1' Xcond (classify_stmt q))
  (STyp: hastyp_stmt c0 c1 q c'), Xcond x /\ s' sp_reg = s1' sp_reg.
Proof.
  induction q; intros; simpl in *;
  inversion STyp; subst; clear STyp.
  - (* Nop *) inversion XS. inversion ESO. subst. clear XS ESO. split.
    fallthrus. assumption.
  - (* Move *) inversion XS. subst. destruct (sp_reg == v);
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
  - (* Seq *) inversion XS; subst; destruct (classify_stmt q1) eqn: C1;
    destruct (classify_stmt q2) eqn: C2; try constructor; inversion XS; subst;
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
    destruct (classify_stmt q1) eqn: C1; destruct (classify_stmt q2) eqn: C2;
    inversion IHq; subst; constructor; solve [reflexivity|assumption].
  - (* Rep *) assert (IHq2: ∀ (s s' : store) (x : option exit)
      (XS : exec_stmt h s q s' x), exec_stack_oper h s q s' x XS (classify_stmt q)).
    intros. eapply IHq; eassumption.
    specialize (classify_rep_stmt_semequiv _ _ _ _ _ _ XS IHq2) as Eq.

    destruct (classify_stmt) eqn: CS; try constructor.
    destruct Eq. assumption. destruct Eq. assumption.
    assumption.
Qed.

Require Import Picinae_i386.
Require Import strchr_i386.
Definition null_state: store := fun _ => VaN 0 0.
Definition classify_stmt_at (p: program) (a: addr): option (N * stack_oper) :=
  match p null_state a with
  | Some (sz, q) => Some (sz, classify_stmt q)
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
  (map (fun a => (a, classify_stmt_at fstat_i386 a)) (addrs 450))).


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
