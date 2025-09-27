Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import Lia ZifyN ZifyNat.
Open Scope N_scope.

Local Ltac gdep H := generalize dependent H.
Require Import Lia ZifyN.
Theorem add_1_l_pred_cancel:
  forall a, 0<a -> 1 + N.pred a = a.
Proof.
  lia.
Qed.

Lemma mod_add_1_cancel_weak:
  forall b c m, (1+b) mod m = (1+c) mod m -> b < m -> c < m -> b mod m = c mod m.
Proof.
  intros. gdep H; gdep c. induction b using N.peano_ind; intros.
  destruct m as [|m]. lia. 
  - destruct m as [m|m|]; try lia.
    + rewrite N.mod_small, N.add_0_r in H; try lia.
      destruct (N.lt_trichotomy c (N.pred (N.pos m~1))) as [Lt | [Eq | Gt]]; try lia.
      rewrite N.mod_small in H; lia.
      rewrite Eq in H. rewrite N.add_1_l, N.succ_pred in H; try lia. rewrite N.mod_same in H; try lia.
    + rewrite N.mod_small, N.add_0_r in H; try lia.
      destruct (N.lt_trichotomy c (N.pred (N.pos m~1))) as [Lt | [Eq | Gt]]; try lia.
      rewrite N.mod_small in H; lia.
  - assert (Help:b<m) by lia; specialize (IHb Help); clear Help.
    destruct c as [|c]. rewrite N.add_0_r in H. destruct m as [|m']; try lia. 
    destruct m' as [m'|m'|]; try lia.
    + assert (Boundm: 1 < N.pos m'~1) by lia; remember (N.pos m'~1) as m eqn:T; clear T m'.
      destruct (N.lt_trichotomy (N.succ b) (N.pred m)) as [LT | [EQ | GT]]; try lia.
      rewrite! N.mod_small in H; try lia.
      rewrite EQ, N.add_1_l, N.succ_pred, N.mod_same, N.mod_small in H; try lia.
    + assert (Boundm: 1 < N.pos m'~0) by lia; remember (N.pos m'~0) as m eqn:T; clear T m'.
      destruct (N.lt_trichotomy (N.succ b) (N.pred m)) as [LT | [EQ | GT]]; try lia.
      rewrite! N.mod_small in H; try lia.
      rewrite EQ, N.add_1_l, N.succ_pred, N.mod_same, N.mod_small in H; try lia.
    + (* case where c is positive *)
      destruct m as [|m']; try lia. destruct m' as [m'|m'|]; only 3: lia.
      * assert (Boundm: 1 < N.pos m'~1) by lia; remember (N.pos m'~1) as m eqn:T; clear T m'.
        assert (Bundc: 0 < N.pos c) by lia; remember (N.pos c) as nc eqn:T; clear T c; rename nc into c.
        assert (Help:N.pred c < m) by lia.
        specialize (IHb (N.pred c) Help); clear Help. enough (Help:(1+b) mod m = (1+N.pred c) mod m). specialize (IHb Help).
        rewrite <-N.add_1_l, <-N.Div0.add_mod_idemp_r, IHb, N.Div0.add_mod_idemp_r, N.add_1_l, N.succ_pred; try lia.
        clear IHb.
        rewrite! N.add_1_l, N.succ_pred, !N.mod_small; try lia. destruct (N.lt_trichotomy (N.succ b) (N.pred m)) as [Ltb | [Eqb | Gtb]];
            destruct (N.lt_trichotomy c (N.pred m)) as [Ltc | [Eqc | Gtc]]; match goal with
                                                                            | H: N.succ b = N.pred m |- _=> idtac
                                                                            | _ => rewrite! N.mod_small in H end; try rewrite Eqb in *;  try rewrite add_1_l_pred_cancel, N.mod_same in *; try lia.
            subst c. rewrite add_1_l_pred_cancel, N.mod_same in H; try lia.
            rewrite N.mod_small in H; try lia.
      * assert (Boundm: 1 < N.pos m'~0) by lia; remember (N.pos m'~0) as m eqn:T; clear T m'.
        assert (Bundc: 0 < N.pos c) by lia; remember (N.pos c) as nc eqn:T; clear T c; rename nc into c.
        assert (Help:N.pred c < m) by lia.
        specialize (IHb (N.pred c) Help); clear Help. enough (Help:(1+b) mod m = (1+N.pred c) mod m). specialize (IHb Help).
        rewrite <-N.add_1_l, <-N.Div0.add_mod_idemp_r, IHb, N.Div0.add_mod_idemp_r, N.add_1_l, N.succ_pred; try lia.
        clear IHb.
        rewrite! N.add_1_l, N.succ_pred, !N.mod_small; try lia. destruct (N.lt_trichotomy (N.succ b) (N.pred m)) as [Ltb | [Eqb | Gtb]];
            destruct (N.lt_trichotomy c (N.pred m)) as [Ltc | [Eqc | Gtc]]; match goal with
                                                                            | H: N.succ b = N.pred m |- _=> idtac
                                                                            | _ => rewrite! N.mod_small in H end; try rewrite Eqb in *;  try rewrite add_1_l_pred_cancel, N.mod_same in *; try lia.
            subst c. rewrite add_1_l_pred_cancel, N.mod_same in H; try lia.
            rewrite N.mod_small in H; try lia.
Qed.

Lemma mod_add_1_cancel:
  forall b c m, (1+b) mod m = (1+c) mod m -> b mod m = c mod m.
Proof.
  intros. destruct (N.eq_0_gt_0_cases m); try rewrite N.mod_0_r in *; try lia.
  assert (Help:m <> 0) by lia.
  pose proof (Eqb:=N.div_mod b _ Help).
  pose proof (Eqc:=N.div_mod c _ Help).
  rewrite Eqb, Eqc in H.
  enough ((1 + b mod m) mod m = (1 + c mod m) mod m).
  epose proof (mod_add_1_cancel_weak _ _ _ H1 _ _). Unshelve. 3-4: now apply N.mod_lt.
  rewrite (N.mod_small (b mod m)), (N.mod_small (c mod m)) in H2; try assumption; try apply N.mod_lt; lia.
  rewrite N.mul_comm, (N.mul_comm _ (c/m)) in H.
  rewrite <-N.add_mod_idemp_r, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  symmetry in H.
  rewrite <-N.add_mod_idemp_r, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  now symmetry in H.
  all: assumption.
Qed.

Lemma mod_add_cancel_l_weak:
  forall a b c m, (a+b) mod m = (a+c) mod m -> b < m -> c < m -> a < m -> b mod m = c mod m.
Proof.
  intros. destruct m. lia.
  assert (0 < N.pos p) by lia; remember (N.pos p) as m eqn:Heq; clear Heq p.
  gdep H; gdep H0; gdep H1; gdep b; gdep c. induction a using N.peano_ind; intros.
  - now rewrite! N.add_0_l in H.
  - assert (Help:a<m) by lia. specialize (IHa Help). rewrite <-!N.add_1_l, <-!N.add_assoc in H.
    enough (ABC: (a+b) mod m = (a+c) mod m). specialize (IHa c b H1 H0 ABC). assumption. clear IHa.
    apply mod_add_1_cancel. assumption. 
Qed.

Lemma mod_add_cancel_l:
  forall a b c m, (a+b) mod m = (a+c) mod m -> b mod m = c mod m.
Proof.
  intros. destruct m. lia.
  assert (0 < N.pos p) by lia; remember (N.pos p) as m eqn:Heq; clear Heq p.
  assert (Help:m <> 0) by lia.
  pose proof (Eqa:=N.div_mod a _ Help).
  pose proof (Eqb:=N.div_mod b _ Help).
  pose proof (Eqc:=N.div_mod c _ Help).
  rewrite Eqb, Eqc in H.
  enough ((a mod m + b mod m) mod m = (a mod m + c mod m) mod m).
  epose proof (mod_add_cancel_l_weak _ _ _ _ H1 _ _ _). Unshelve. 3-5: now apply N.mod_lt.
  rewrite (N.mod_small (b mod m)), (N.mod_small (c mod m)) in H2; try assumption; try apply N.mod_lt; lia.
  rewrite N.mul_comm, (N.mul_comm _ (c/m)) in H.
  rewrite <-N.add_mod_idemp_r, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  symmetry in H.
  rewrite <-N.add_mod_idemp_r, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  rewrite Eqa in H. rewrite N.mul_comm in H.
  rewrite <-N.add_mod_idemp_l, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  symmetry in H.
  rewrite <-N.add_mod_idemp_l, <-(N.add_mod_idemp_l (N.mul _ _)), N.Div0.mod_mul, N.add_0_l, N.mod_mod in H.
  all: assumption.
Qed.

Lemma mod_add_same_r : forall a b c m,
  (a + b) mod m = (a + c) mod m ->
  b < m ->
  c < m ->
  b = c.
Proof.
  intros. apply mod_add_cancel_l in H. rewrite !N.mod_small in H. all:assumption.
Qed.
