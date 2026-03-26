Require Import Picinae_core.
Require Import NArith.
Require Import List.
Open Scope N.

Module Type PICINAE_OPTIMIZER (Arch: PICINAE_IL).

Import Arch.

Print N.eqb.
(* Let's start with a simpler example: reduce binop *)
Fixpoint rbinop_exp (e:exp) : exp :=
  match e with
  | Var _
  | Word _ _ => e
  | Load e1 e2 en w => Load (rbinop_exp e1) (rbinop_exp e2) en w
  | Store e1 e2 e3 en w => Store (rbinop_exp e1) (rbinop_exp e2) (rbinop_exp e3) en w
  | BinOp b (Word n1 w1) (Word n2 w2) =>
      if N.eqb w1 w2 then Word (eval_binop b w1 n1 n2) (widthof_binop b w1)
      else e
  | BinOp b e1 e2 => BinOp b (rbinop_exp e1) (rbinop_exp e2)
  | UnOp u e => UnOp u (rbinop_exp e)
  | Cast c w e => Cast c w (rbinop_exp e)
  | Let v e1 e2 =>
    (* Strong version: subst_exp (update valof v (Some (rbinop_exp e1))) e2 *)
    Let v (rbinop_exp e1) (rbinop_exp e2)
  | Unknown w => Unknown w
  | Ite e1 e2 e3 => Ite (rbinop_exp e1) (rbinop_exp e2) (rbinop_exp e3)
  | Extract n1 n2 e => Extract n1 n2 (rbinop_exp e)
  | Concat e1 e2 => Concat (rbinop_exp e1) (rbinop_exp e2)
  end.

(* Didn't figure out how to pass a list to gen_deps *)
Local Ltac gen_deps Ds :=
    match Ds with
    | nil => idtac
    | ?d :: ?ds => generalize dependent d; gen_deps ds
    end.
Local Ltac gdep d := generalize dependent d.
Local Ltac inv H := inversion H; subst; clear H.
Local Ltac appIH := repeat match goal with
               | [IH: context[eval_exp _ _ (rbinop_exp ?e) _ _ ->_],
                  H: eval_exp _ _ (rbinop_exp ?e) _ _ |- _] => apply IH in H
               end.
Local Ltac invreduct := match goal with
  | [H: context[rbinop_exp _] |- _] => inv H
  end.
Local Ltac rwclear H := rewrite H in *; clear H.

Lemma fold_loadx:
  forall e1 e2 en w,
    Load (rbinop_exp e1) (rbinop_exp e2) en w = rbinop_exp (Load e1 e2 en w).
Proof. reflexivity. Qed.

Lemma fold_storex:
  forall e1 e2 e3 en w,
    Store (rbinop_exp e1) (rbinop_exp e2) (rbinop_exp e3) en w = rbinop_exp (Store e1 e2 e3 en w).
Proof. reflexivity. Qed.

Lemma eval_exp_w_det:
  forall c s e n w1 w2,
    eval_exp c s e n w1 -> eval_exp c s e n w2 -> w1 = w2.
Proof.
  intros c s e n w1 w2 D; gdep w2; induction D; intros w2' D'; inv D'; try reflexivity.
    rewrite TYP in TYP0. inv TYP0; reflexivity.
Admitted.



Theorem rbinop_exp_correct:
  forall e e' (c:typctx) (s:store) n w
    (Heq: e' = rbinop_exp e),
    eval_exp c s e n w <-> eval_exp c s e' n w.
Proof.
  intros; subst; split.
  + intro DERIV; induction DERIV; simpl (rbinop_exp _);
    try econstructor; try assumption;
      match goal with
      | [H: eval_exp ?c ?s _ _ _ |- eval_exp ?c ?s _ _ _] => exact H
      | _ => idtac
      end.
    (* A good example of simple automation solving all but 1 of the 200+ goals. *)
    - destruct e1; destruct e2; simpl (rbinop_exp _); try assumption; try constructor; try assumption.
       inversion DERIV1; inversion DERIV2; subst.
       rewrite N.eqb_refl. constructor.
  + gdep w; gdep n; gdep s; gdep c.
    induction e; intros dc ds dn dw D; simpl (rbinop_exp _) in D;
     try assumption; inversion D; subst;
     appIH ; try econstructor; try assumption;
      try match goal with
      | [H: ?e = _ |-_] => match e with
                           | Word _ _ => idtac | BinOp _ _ _ => idtac
                           | _=> destruct e1; destruct e2; try destruct (_ =? _); try discriminate
                           end
      end.
    - destruct e1; destruct e2; try destruct (_ =? _) eqn:E; try discriminate.
      inversion H0. subst. clear H0. apply Neqb_ok in E. subst; repeat constructor.
    - enough (b=bop); try subst. eapply EBinOp.
        eapply IHe1. destruct e1; try solve [inversion H0; subst; assumption].
          destruct e2; try solve [inversion H0; subst; assumption].
          destruct (w0 =? w1); inversion H0; subst; try assumption.
        eapply IHe2. destruct e2; try solve [inversion H0; subst; assumption].





      match goal with
      |- ?g => assert (SOLV: e0 = rbinop_exp e1 -> e3 = rbinop_exp e2 -> g)
      end.
      { intros; subst. destruct e1 eqn:E1eq; cycle 1. destruct e2; cycle 1.
        destruct (w0 =? w1) eqn:Weq;[apply Neqb_ok in Weq| rewrite N.eqb_neq in Weq]; subst.
          discriminate.
          contradiction Weq. inversion D. inv E0; inv E3; now subst.
        (* Now we've dealt with the special case, these should all be recursively correct. *)
        appIH. inv H0. inv D. rwclear H4. inv E1; inv E0. apply EBinOp.
          constructor.
          rewrite fold_loadx in E3. apply IHe2 in E3. assumption.
        appIH. inv H0. inv D. rwclear H4. rewrite fold_storex in E3. appIH. inv E3.
          inv E1; inv E2. inv E4; inv E1; inv E5; inv E3; inv E6; inv E7.

          rwclear H.
          clear H1 H4.
        all: inv H0; inv D; appIH. all: try invreduct; appIH.
        inv H0. inv D. constructor.

      destruct e1; destruct e2; try destruct (_ =? _) eqn:E; try discriminate.

      14: { inv H0. apply N.eqb_neq in E. contradiction E. inv E1; inv E2; now subst. }
      all: simpl (rbinop_exp _) in H0; inversion H0; subst; try constructor; try assumption. inversion D.
      all:
      apply Neqb_ok in E; subst. inversion H0; subst. constructor; constructor.
    -

(* A weak version where we don't eliminate Let *)
Fixpoint subst_exp (valof : var -> option exp) exp :=
  match exp with
  | Var v => match valof v with
             | Some e => e
             | None => Var v
             end
  | Word n w => exp
  | Load e1 e2 en w => Load (subst_exp valof e1) (subst_exp valof e2) en w
  | Store e1 e2 e3 en w => Store (subst_exp valof e1) (subst_exp valof e2) (subst_exp valof e3) en w
  | BinOp b e1 e2 => BinOp b (subst_exp valof e1) (subst_exp valof e2)
  | UnOp u e => UnOp u (subst_exp valof e)
  | Cast c w e => Cast c w (subst_exp valof e)
  | Let v e1 e2 =>
    (* Strong version: subst_exp (update valof v (Some (subst_exp valof e1))) e2 *)
    Let v (subst_exp valof e1) e2
  | Unknown w => Unknown w
  | Ite e1 e2 e3 => Ite (subst_exp valof e1) (subst_exp valof e2) (subst_exp valof e3)
  | Extract n1 n2 e => Extract n1 n2 (subst_exp valof e)
  | Concat e1 e2 => Concat (subst_exp valof e1) (subst_exp valof e2)
  end.

Theorem subst_exp_empty:
  forall e, e = subst_exp (fun v => None) e.
Proof.
  intros; induction e; simpl (subst_exp _ _);
    repeat match goal with
    | [EQ: ?e = subst_exp _ ?e |- context[subst_exp _ ?e]] => rewrite <-EQ
    | _ => idtac
    end; try reflexivity.
Qed.

Theorem subst_exp_correct:
  forall e e' (c:typctx) (s:store) n w
    (Heq: e' = subst_exp (fun v => None) e),
    eval_exp c s e n w <-> eval_exp c s e' n w.
Proof.
  intros. subst; rewrite <-subst_exp_empty. reflexivity.
Qed.

Fixpoint subst_stmt (valof : var -> option exp) (s:stmt) : (stmt * (option (var -> option exp))) :=
  match s with
  | Nop => (Nop, Some valof)
  | Move v e => (Move v (subst_exp valof e), Some (update valof v (Some (subst_exp valof e))))
  | Jmp e => (Jmp (subst_exp valof e), Some valof)
  | Exn i => (Exn i, Some valof)
  | Seq q1 q2 =>
    match subst_stmt valof q1 with
    | (q, None) => (Seq q q2, None)
    | (q1', Some valof') => match subst_stmt valof' q2 with
                          | (q2', valof'') => (Seq q1' q2', valof'')
                          end
    end
   (* The effects of If and Rep can't be predicted statically,
      so they terminate the recursion *)
  | If e q1 q2 => (If (subst_exp valof e) (fst (subst_stmt valof q1)) (fst (subst_stmt valof q2)),
                   None)
  | Rep e q => (Rep (subst_exp valof e) q, None)
  end.

(* Make an inductive prop sort of like a type context that eats a
   statement piece by piece *)

Inductive gobble : stmt -> (var -> bool) -> Prop :=
  | GMove v e : gobble (Move v e) (vareqb v)
  | GSeq q1 vb (G1 : gobble q1 vb) q2 : gobble (Seq q1 q2) vb
  | GOther q (F: match q with | Move _ _ | Seq _ _ => False | _ => True end) :
      gobble q (fun _ => false).


Theorem subst_stmt_correct:
  forall stmt stmt' (c c':typctx) (s s':store) (ox:option exit)
    (Heq: stmt' = fst (subst_stmt (fun _ => None) stmt)),
    exec_stmt c s stmt c' s' ox <-> exec_stmt c s stmt' c' s' ox.
Proof.
  Local Ltac inv H := inversion H; subst.
  induction stmt0; intros; subst; simpl (fst _); try rewrite <-subst_exp_empty; try easy.
  - (* Seq *)
    split.
    + intro H.
      remember (subst_stmt (fun _ : var => None) stmt0_1) as stmt1'.
      destruct stmt1' as [stmt1' [valof'|] ].
      remember (subst_stmt valof' stmt0_2) as stmt2'.
      destruct stmt2' as [stmt2' [valof''|] ].
      all: simpl (fst _).
      -- inv H. econstructor. now apply IHstmt0_1. econstructor. apply IHstmt0_1;[reflexivity | exact XS1].
Abort.

Theorem subst_stmt_correct:
  forall stmt stmt' (c c':typctx) (s s':store) (ox:option exit),
    exists (valof:var->option exp),
    (stmt' = fst (subst_stmt valof stmt)) ->
    exec_stmt c s stmt c' s' ox <-> exec_stmt c s stmt' c' s' ox.
Proof.
  induction stmt0; intros; exists (fun _ => None); intros; subst; simpl (fst _); try rewrite <-subst_exp_empty; try easy.
  - (* Seq *)
    remember (subst_stmt (fun _ : var => None) stmt0_1) as stmt1'.
    destruct stmt1' as [stmt1' [valof'|] ].
    remember (subst_stmt valof' stmt0_2) as stmt2';
    destruct stmt2' as [stmt2' [valof''|] ].
    all: simpl (fst _). subst.
    + split; intro D; inv D; econstructor.
      clear IHstmt0_2 Heqstmt2'.
      specialize (IHstmt0_1 stmt1' c c' s s' (Some x)).
      destruct IHstmt0_1 as [IHvalof IH]. apply IH.
Abort.

Theorem subst_stmt_correct:
  forall stmt stmt' (c c':typctx) (s s':store) (ox:option exit),
    exists (valof:var->option exp),
    (stmt' = fst (subst_stmt valof stmt)) ->
    exec_stmt c s stmt c' s' ox <-> exec_stmt c s stmt' c' s' ox.
Proof.
  induction stmt0; intros.
















