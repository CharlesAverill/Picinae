Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import PArith.
Require Import Picinae_armv7.
Require Import memset_arm.

Import ARMNotations.
Open Scope N.

Definition xcomp n := ((2^32 - (n mod (2^32))) mod (2^32)).
Notation "⊖ x" := (xcomp x) (at level 20).
Notation "x _⊖_ y" := (x ⊕ ⊖y) (at level 50, left associativity).

Theorem xminus_zero n : n _⊖_ n = 0.
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite <- N.add_mod_idemp_l by discriminate.
  rewrite N.add_comm.
  rewrite N.sub_add by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  reflexivity.
Qed.

Theorem xminus_alt' n m : m < 2^32 -> 2 ^ 32 + n ⊖ m = n mod (2^32) _⊖_ m.
  intro H.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc; auto using N.lt_le_incl.
  unfold xcomp.
  rewrite (N.mod_small m) by assumption.
  rewrite N.add_mod_idemp_l by discriminate.
  rewrite N.add_mod_idemp_r by discriminate.
  reflexivity.
Qed.

Theorem xminus_alt n m : n < 2^32 -> m < 2^32 -> 2 ^ 32 + n ⊖ m = n _⊖_ m.
  intros H1 H2.
  rewrite xminus_alt' by assumption.
  rewrite (N.mod_small n) by assumption.
  reflexivity.
Qed.

Theorem mod_n_n (n d:N) : d ≠ 0 -> (n mod d) mod d = n mod d.
  intro H.
  apply N.mod_small.
  apply N.mod_upper_bound.
  exact H.
Qed.

Theorem xcomp_mod n : ⊖n mod (2^32) = ⊖n.
  unfold xcomp.
  apply mod_n_n.
  discriminate.
Qed.

Theorem xcomp_mod_in n : ⊖(n mod (2^32)) = ⊖n.
  unfold xcomp.
  rewrite mod_n_n by discriminate.
  reflexivity.
Qed.

Theorem xplus_minus n m : m < n -> (n-m) mod (2^32) = n _⊖_ m.
  intros.
  assert (Q : m / (2^32) <= n / (2^32)).
  apply N.div_le_mono; try discriminate.
  apply N.lt_le_incl.
  assumption.
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc by
      (apply N.lt_le_incl; eapply N.le_lt_trans; try exact H;
       apply N.mod_le; discriminate).
  rewrite mod_add_l by discriminate.
  rewrite (N.div_mod m (2^32)) at 1 by discriminate.
  rewrite N.sub_add_distr.
  rewrite (N.div_mod n (2^32)) by discriminate.
  rewrite N.add_sub_swap by (apply N.mul_le_mono_l; exact Q).
  rewrite <- N.mul_sub_distr_l.
  rewrite N.lt_eq_cases in Q.
  destruct Q as [Q|Q]; [|rewrite Q].
  rewrite <- N.add_0_l in Q at 1.
  rewrite N.lt_add_lt_sub_r in Q.
  destruct (n / 2^32); try discriminate.
  destruct (_ - m/_); try discriminate.
  rewrite <- (N.succ_pos_pred p0).
  rewrite <- (N.succ_pos_pred p).
  repeat rewrite N.mul_succ_r.
  repeat rewrite <- N.add_assoc.
  repeat rewrite (N.add_comm (2^32)).
  repeat rewrite <- (N.add_sub_assoc (_*_)) by
      (eapply N.le_trans; [apply N.lt_le_incl,N.mod_upper_bound; discriminate|
                           rewrite N.add_comm; apply N.le_add_r]).
  repeat rewrite mod_add_mul_ll by discriminate.
  reflexivity.
  rewrite N.sub_diag.
  rewrite N.add_0_l.
  rewrite <- N.add_sub_assoc; [symmetry; apply mod_add_mul_ll; discriminate|].
  rewrite (N.div_mod' n (2^32)) in H.
  rewrite (N.div_mod' m (2^32)) in H.
  rewrite Q in H.
  apply N.lt_le_incl.
  eapply N.add_lt_mono_l.
  exact H.
Qed.

Theorem xcomp_plus_dist' n m : ⊖n ⊕ ⊖m = ⊖(n+m).
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_mod_idemp_l by discriminate.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite N.add_comm.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite <- N.sub_add_distr.
  rewrite xplus_minus by
      (apply N.add_lt_mono; apply N.mod_upper_bound; discriminate).
  rewrite <- N.add_mod_idemp_l at 1 by discriminate.
  rewrite N.add_0_l.
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_mod_idemp_l by discriminate.
  apply mod_n_n.
  discriminate.
Qed.

Theorem xcomp_plus_dist n m : ⊖n ⊕ ⊖m = ⊖(n⊕m).
  rewrite xcomp_plus_dist'.
  unfold xcomp.
  rewrite mod_n_n by discriminate.
  reflexivity.
Qed.

Theorem xplus_id_l' n : n ⊕ 0 = n mod 2^32.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplus_id_l n : n < 2^32 -> n ⊕ 0 = n.
  rewrite N.add_0_r.
  apply N.mod_small.
Qed.

Theorem xplus_id_r' n : 0 ⊕ n = n mod 2^32.
  reflexivity.
Qed.

Theorem xplus_id_r n : n < 2^32 -> 0 ⊕ n = n.
  apply N.mod_small.
Qed.

Theorem xplus_comm n m : n ⊕ m = m ⊕ n.
  rewrite N.add_comm.
  reflexivity.
Qed.

Lemma xplus_assoc : forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c.
  simpl.
  intros.
  rewrite N.add_mod_idemp_r, N.add_mod_idemp_l, N.add_assoc;
    reflexivity + discriminate.
Qed.

Theorem mod_greater (n d1 d2:N) :
  d1 ≠ 0 -> d1 <= d2 -> (n mod d1) mod d2 = n mod d1.
  intros.
  apply N.mod_small.
  eapply N.lt_le_trans; eauto.
  apply N.mod_upper_bound.
  exact H.
Qed.

Fixpoint posmod2 p w :=
  match p,w with
  | xH,_ | xI _,xH => 1
  | xO _,xH => 0
  | xO p',_ => N.double (posmod2 p' (Pos.pred w))
  | xI p',_ => N.succ (N.double (posmod2 p' (Pos.pred w)))
  end.

Definition mod2 n w :=
  match n,w with | 0,_ | _,0 => 0 | N.pos n',N.pos w' => posmod2 n' w' end.

Theorem npossucc p : N.pos (Pos.succ p) = N.succ (N.pos p). auto. Qed.

Theorem mod2_eq : forall n w, mod2 n w = n mod 2^w.
  destruct n as [|n],w as [|w]; auto using N.mod_1_r.
  unfold mod2.
  generalize dependent n.
  induction w using Pos.peano_ind.
  intros.
  rewrite <- N.bit0_mod.
  simpl.
  destruct n; reflexivity.
  intros.
  rewrite npossucc.
  rewrite N.pow_succ_r; try discriminate.
  rewrite N.mod_mul_r; try discriminate.
  simpl.
  rewrite <- N.div2_div.
  rewrite <- N.bit0_mod.
  destruct n; simpl; try rewrite Pos.pred_succ; try rewrite IHw; simpl; auto;
    destruct (_ mod _),w; simpl; reflexivity.
Qed.

Theorem xplusid' : forall n, n ⊕ 0 = n mod 2^32.
  intro n.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplusinv' : forall b c, b < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c mod 2^32.
  intros.
  rewrite (N.add_comm (2^32)).
  rewrite N.add_comm.
  destruct b.
  rewrite N.add_0_r.
  rewrite N.sub_0_r.
  rewrite mod_add_r; try discriminate.
  apply mod_n_n.
  discriminate.
  assert (N.pos p <= 2^32); auto using N.lt_le_incl.
  rewrite <- N.add_sub_assoc; auto.
  rewrite <- xplus_assoc.
  rewrite N.sub_add; auto.
  rewrite N.mod_same; try discriminate.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplusinv : forall b c, b < 2^32 -> c < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c.
  intros.
  rewrite xplusinv'; auto.
  apply N.mod_small.
  assumption.
Qed.

Theorem minus_n_mod_n n m : 0 < m -> m < n -> (n - m) mod m = n mod m.
  intros H0 H1.
  rewrite (N.div_mod' n m) at 1.
  assert (Q : m <= m * (n / m)).
  rewrite <- N.mul_1_r at 1.
  apply N.mul_le_mono_pos_l; [exact H0|].
  destruct m; inversion H0.
  apply N.div_le_lower_bound; [discriminate|].
  rewrite N.mul_1_r.
  apply N.lt_le_incl.
  exact H1.
  rewrite N.add_sub_swap by exact Q.
  rewrite <- N.mul_pred_r.
  destruct m; inversion H0.
  rewrite mod_add_mul_ll by discriminate.
  apply mod_n_n.
  discriminate.
Qed.

Theorem xcomp_comp n : n < 2^32 -> ⊖(⊖n) = n.
  intro H.
  rewrite <- (xplus_id_l n) at 2 by assumption.
  rewrite <- (xminus_zero (⊖n)).
  rewrite xplus_assoc.
  fold (n _⊖_ n).
  rewrite xminus_zero.
  rewrite xplus_id_r by (apply N.mod_upper_bound; discriminate).
  reflexivity.
Qed.

Theorem xeq_xplus_r n m p :
  n < 2^32 -> p < 2^32 -> n ⊕ m = p <-> n = p _⊖_ m.
  intros.
  split; intros; subst; rewrite <- xplus_assoc; [|rewrite (N.add_comm _ m)];
    rewrite xminus_zero; rewrite xplus_id_l by assumption;
      reflexivity.
Qed.

Theorem xeq_xplus_l n m p :
  m < 2^32 -> p < 2^32 -> n ⊕ m = p <-> m = ⊖n ⊕ p.
  intros.
  rewrite xplus_comm.
  rewrite xeq_xplus_r by assumption.
  rewrite xplus_comm.
  reflexivity.
Qed.

Theorem xeq_xcomp_r n m p :
  n < 2^32 -> p < 2^32 -> n _⊖_ m = p <-> n = p ⊕ m.
  intros.
  rewrite xeq_xplus_r by assumption.
  rewrite <- (xcomp_mod_in m).
  rewrite xcomp_comp by (apply N.mod_upper_bound; discriminate).
  rewrite N.add_mod_idemp_r by discriminate.
  reflexivity.
Qed.

Theorem xeq_xcomp_l n m p :
  m < 2^32 -> p < 2^32 -> ⊖n ⊕ m = p <-> m = n ⊕ p.
  intros.
  rewrite xplus_comm.
  rewrite xeq_xcomp_r by assumption.
  rewrite xplus_comm.
  reflexivity.
Qed.

Theorem xplus_minus' n m : m <= n → n ⊖ m = n _⊖_ m.
  intro H.
  rewrite N.lt_eq_cases in H.
  destruct H; [apply xplus_minus; assumption|].
  subst.
  rewrite xminus_zero.
  rewrite N.sub_diag.
  reflexivity.
Qed.

Theorem xplus_minus'' n m :
  n < 2^32 -> m <= n → n - m = n _⊖_ m.
  intros H0 H1.
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl,N.mod_upper_bound; discriminate).
  rewrite N.add_comm.
  assert (H2 : m < 2^32) by (eapply N.le_lt_trans; eassumption).
  rewrite (N.mod_small m) by (eapply N.le_lt_trans; eassumption).
  rewrite <- N.add_sub_assoc by assumption.
  rewrite mod_add_l by discriminate.
  symmetry.
  apply N.mod_small.
  eapply N.le_lt_trans ; [|exact H0].
  apply N.le_sub_l.
Qed.

Theorem xlt_minus n m p :
  n < 2^32 -> n _⊖_ m < p -> n < p + m.
  intros H1 H2.
  destruct (N.lt_ge_cases n m) as [H3|H3].
  eapply N.lt_le_trans; [exact H3|].
  rewrite N.add_comm.
  apply N.le_add_r.
  rewrite <- xplus_minus'' in H2 by assumption.
  apply N.lt_sub_lt_add_r.
  assumption.
Qed.

Theorem sub_eq_r n m p : n <= m -> p <= m - n <-> p + n <= m.
  intro H0.
  rewrite N.add_le_mono_r.
  rewrite N.sub_add by exact H0.
  reflexivity.
Qed.

Theorem xminus_eq_r n m p :
  n < 2^32 -> m <= n -> p <= n _⊖_ m <-> p + m <= n.
  intros H0 H1.
  rewrite <- xplus_minus'' by assumption.
  apply sub_eq_r.
  assumption.
Qed.

Theorem andshiftlzero' : forall a b w,
    (a mod 2^w) .& (b << w) = 0.
  destruct a,b,w; try rewrite N.mod_1_r;
    try rewrite N.shiftl_0_l,N.land_0_r; auto.
  rewrite <- mod2_eq.
  simpl.
  generalize dependent p.
  generalize dependent p0.
  induction p1 using Pos.peano_ind; simpl; auto.
  destruct p; reflexivity.
  destruct p; simpl; try rewrite Pos.pred_succ; rewrite Pos.iter_succ; auto;
    destruct (Pos.succ p1); auto; specialize (IHp1 p0 p);
      destruct posmod2; auto; simpl in *; rewrite IHp1; reflexivity.
Qed.

Theorem andshiftlzero : forall a b w,
    a < 2^w -> a .& (b << w) = 0.
  intros a b w.
  rewrite <- N.shiftl_1_l.
  destruct a,b,w; simpl; auto.
  intros.
  destruct p; discriminate.
  unfold N.lt.
  simpl.
  generalize dependent p0.
  generalize dependent p.
  induction p1 using Pos.peano_ind; simpl; auto.
  intros.
  destruct p; simpl; auto.
  destruct p; inversion H.
  destruct p; inversion H.
  intros a b.
  repeat rewrite Pos.iter_succ.
  intros.
  destruct a; simpl; auto; rewrite IHp1; auto.
  generalize dependent (Pos.iter xO 1%positive p1).
  intros.
  clear IHp1.
  fold (N.compare (N.pos a) (N.pos p)).
  fold (N.lt (N.pos a) (N.pos p)).
  rewrite N.mul_lt_mono_pos_l.
  repeat rewrite <- N.double_spec.
  simpl.
  eapply N.lt_trans.
  apply N.lt_succ_diag_r.
  simpl.
  auto.
  reflexivity.
Qed.

Ltac isPos n :=
  match n with
  | xH => true
  | xO ?n => isPos n
  | xI ?n => isPos n
  | _ => false
  end.

Ltac isN n :=
  match n with
  | N.pos ?n => isPos n
  | 0 => true
  | _ => false
  end.

Require Import Quote.

Print Quote.
(* Print  *)
(* Print varmap. *)
Inductive sumQuote :=
| SQPlus : sumQuote -> sumQuote -> sumQuote
| SQZ : sumQuote
| SQV : index -> sumQuote.

Fixpoint sumDenote (vars : varmap N) (l : sumQuote) : N :=
  match l with
  | SQPlus n m => sumDenote vars n + sumDenote vars m
  | SQZ => 0
  | SQV v => varmap_find 0 v vars
  end.

Inductive sumeqQuote :=
| SQEq : sumQuote -> sumQuote -> sumeqQuote.

Fixpoint sumEqDenote (vars : varmap N) (q : sumeqQuote) : Prop :=
  match q with SQEq n m => sumDenote vars n = sumDenote vars m end.

Ltac id n := n.
Ltac idtacp n := idtac n.
Ltac idpose n := pose n.

Locate "++".
Search "app".
Fixpoint sdflatten sd :=
  match sd with
  | SQV v => cons v nil
  | SQZ => nil
  | SQPlus sda sdb => app (sdflatten sda) (sdflatten sdb)
  end.

Fixpoint sdlistdenote vars l :=
  match l with
  | cons v nil => varmap_find 0 v vars
  | cons v l' => varmap_find 0 v vars + sdlistdenote vars l'
  | nil => 0
  end.

Theorem sdflatappend vars sd1 sd2 :
  sdlistdenote vars (sd1 ++ sd2) = sdlistdenote vars sd1 + sdlistdenote vars sd2.
  induction sd1; auto.
  simpl.
  destruct sd1; simpl in *.
  destruct sd2; try reflexivity.
  symmetry.
  apply N.add_0_r.
  rewrite IHsd1.
  apply N.add_assoc.
Qed.

Theorem sdflatprove vars sd : sumDenote vars sd = sdlistdenote vars (sdflatten sd).
  induction sd; simpl; auto using N.add_0_r.
  rewrite sdflatappend.
  rewrite IHsd1,IHsd2.
  reflexivity.
Qed.

(* Ltac sdflattac n := *)
(*   let x := n in rewrite (sdflatprove x). *)
(* Ltac sdflattac n := *)
(*   let x := n in rewrite (sdflatprove _ x). *)
Ltac sdflattac n :=
  match n with
    sumDenote ?vars ?sd =>
    pose (sdflatprove vars sd)
  end.
Ltac sdflattac2 n :=
  match n with
    sumDenote ?vars ?sd =>
    let x := eval simpl in (sdflatprove vars sd) in pose x
  end.
Ltac sdflattac3 n :=
  match n with
    sumDenote ?vars ?sd =>
    pose (x := sdflatprove vars sd); simpl in x; rewrite x; clear x
  end.
  (* let x := n in rewrite sdflatprove in n. *)

Fixpoint sdlistdenote' vars l :=
  match l with
  | cons v nil => varmap_find 0 v vars
  | cons v l' => sdlistdenote' vars l' + varmap_find 0 v vars
  | nil => 0
  end.

Theorem sdflatappend' vars sd1 sd2 :
  sdlistdenote' vars (sd1 ++ sd2) = sdlistdenote' vars sd1 + sdlistdenote' vars sd2.
  induction sd1; auto.
  simpl.
  rewrite IHsd1.
  destruct sd1.
  destruct sd2; auto using N.add_0_r.
  simpl.
  apply N.add_comm.
  simpl.
  repeat rewrite <- N.add_assoc.
  f_equal.
  apply N.add_comm.
Qed.

Theorem sdflatprove' vars sd : sumDenote vars sd = sdlistdenote' vars (sdflatten sd).
  induction sd; try reflexivity.
  simpl.
  rewrite IHsd1,IHsd2.
  symmetry.
  apply sdflatappend'.
Qed.

Ltac sdflattac' n :=
  match n with
    sumDenote ?vars ?sd =>
    pose (x := sdflatprove' vars sd); simpl in x; rewrite x; clear x
  end.

Ltac sdflattac'' n :=
  match n with
    sumDenote ?vars ?sd =>
    pose (x := sdflatprove' vars sd); simpl in x; rewrite x
  end.

Theorem okay n m p : (* n + (m - p) + *) 0 = m + (n + p).
  (* quote sumDenote in (n+(m-p)+0) using idpose. *)
  (* quote sumDenote in (n+(m-p)+0) using sdflattac2. *)
  match goal with
    |- context [?x+?y] => quote sumDenote in (x+y) using sdflattac'
  end.
  quote sumDenote in (n+(m-p)+0) using sdflattac3.
  simpl in e.
  rewrite e.
  match goal with
  (* | |- context [?x+?y] => idtac x y *)
  (* | |- context [?x+?y] => quote sumDenote in (x+y) using rewrite sdflattac *)
  end.
  Print Quote.
  quote n.
  let x := quote n in idtac n.
  let n := index_eq n n in idtac n.
  let n := (isN false) in idtac n.
  let n := (isN 0) in idtac n.
  let n := (isN 5) in idtac n.
  let n := (isN 1) in idtac n.
  idtac (constr:(isnum 5)).
  match goal with _ := ?x |- _ => (idtac constr:(isnum x)) end.
  idtac (eval simpl in (isnum x)).