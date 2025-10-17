 (* Picinae: Platform In Coq for INstruction Analysis of Executables      ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2025 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Interpreter Theory module:                          MMMMMMMMMMMMMMMMM^NZMMN+Z
   * theory of store-updates and memory-accesses,       MMMMMMMMMMMMMMM/.$MZM8O+
   * theory of two's-complement binary numbers,          MMMMMMMMMMMMMM7..$MNDM+
   * determinism of Unknown-free programs,                MMDMMMMMMMMMZ7..$DM$77
   * monotonicity of stores,                               MMMMMMM+MMMZ7..7ZM~++
   * boundedness of While-free programs,                    MMMMMMMMMMM7..ZNOOMZ
   * inductive schemas for program analysis, and             MMMMMMMMMM$.$MOMO=7
   * frame theorems for assignment-free programs.             MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
   To compile this module, first load the Picinae_core         $ZMMMMMMZ..MMMOMZ
   module and compile it with menu option                       ?MMMMMM7..MNN7$M
   Compile->Compile_buffer.                                      ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import FunctionalExtensionality.
Require Import List.
Require Setoid.
Open Scope list_scope.


(* Define some tactics for reasoning about IL variable identifier equalities
   of the form "v1 == v2", which asserts that v1 and v2 are the same IL var. *)

(* Tactic "vreflexivity v" reduces "v==v" to true (actually "left _"). *)
Theorem iseq_refl {A} {_:EqDec A}:
  forall (x:A), exists (H: x = x), (x == x) = left H.
Proof.
  intro. destruct (x == x).
    eexists. reflexivity.
    contradict n. reflexivity.
Qed.

Ltac vreflexivity v :=
  let H := fresh in
  let t Hveq :=
    destruct (iseq_refl v) as [Hveq H];
    rewrite H in *;
    clear H; try clear Hveq
  in first [ let Hveq := fresh "H" v "eq" in t Hveq
           | let Hveq := fresh "Heq" in t Hveq ].

(* Tactic "vantisym v1 v2" reduces "v1==v2" to false (actually "right _")
   and introduces a subgoal of "v1<>v2". *)
Theorem iseq_antisym {A} {_:EqDec A}:
  forall (x y:A), x<>y -> exists (H: x<>y), (x == y) = right H.
Proof.
  intros. destruct (x == y).
    contradict H. assumption.
    eexists. reflexivity.
Qed.

Tactic Notation "vantisym" constr(v1) constr(v2) :=
  let H1 := fresh in let H2 := fresh in
  let t Hneq :=
    enough (H1: v1 <> v2);
    [ destruct (iseq_antisym v1 v2 H1) as [Hneq H2];
      rewrite H2 in *;
      clear H1 H2; try clear Hneq |]
  in first [ let Hneq := fresh "H" v1 "neq" in t Hneq
           | let Hneq := fresh "Hneq" in t Hneq ].

Tactic Notation "vantisym" constr(v1) constr(v2) "by" tactic(T) :=
  vantisym v1 v2; [|solve T].


(* Define the partial order of A-to-B partial functions ordered by subset. *)

Definition pfsub {A B:Type} (f g: A -> option B) : Prop :=
  forall x y, f x = Some y -> g x = Some y.

Notation "f ⊆ g" := (pfsub f g) (at level 70, right associativity).

Theorem pfsub_refl {A B}: forall (f:A->option B), f ⊆ f.
Proof. unfold pfsub. intros. assumption. Qed.

Theorem pfsub_antisym {A B}:
  forall (f g:A->option B), f ⊆ g -> g ⊆ f -> f = g.
Proof.
  unfold pfsub. intros f g FG GF. extensionality v.
  specialize (FG v). specialize (GF v). destruct (f v) as [b|].
    symmetry. apply FG. reflexivity.
    destruct (g v). apply GF. reflexivity. reflexivity.
Qed.

Theorem pfsub_trans {A B}:
  forall (f g h:A->option B), f ⊆ g -> g ⊆ h -> f ⊆ h.
Proof. unfold pfsub. intros f g h FG GH x y FX. apply GH,FG. assumption. Qed.

Theorem pfsub_contrapos {A B}:
  forall (f g: A -> option B) x, f ⊆ g -> g x = None -> f x = None.
Proof.
  unfold pfsub. intros f g x SS H. specialize (SS x). destruct (f x).
    symmetry. rewrite <- H. apply SS. reflexivity.
    reflexivity.
Qed.

Add Parametric Relation {A B:Type}: (A -> option B) pfsub
  reflexivity proved by pfsub_refl
  transitivity proved by pfsub_trans
as pfsubset.

(* Symmetric updates preserve the partial order relation. *)
Theorem pfsub_update {A B} {_: EqDec A}:
  forall (f g: A -> option B) (SS: f ⊆ g) (x:A) (y:option B),
  update f x y ⊆ update g x y.
Proof.
  intros. unfold update. intros z y' H. destruct (z == x).
    assumption.
    apply SS. assumption.
Qed.

Definition updateall {A B:Type} (f g: A -> option B) (x:A) : option B :=
  match g x with None => f x | Some y => Some y end.

Theorem updateall_subset {A B}:
  forall (f g: A->option B), f ⊆ g -> updateall g f = g.
Proof.
  unfold pfsub, updateall. intros.
  apply functional_extensionality. intro x. specialize H with (x:=x). destruct (f x).
    symmetry. apply H. reflexivity.
    reflexivity.
Qed.

Theorem subset_updateall {A B}:
  forall (f g: A->option B), f ⊆ updateall g f.
Proof. unfold pfsub, updateall. intros. rewrite H. reflexivity. Qed.

Theorem updateall_mono {A B}:
  forall (f1 f2 g: A -> option B) (SS: f1 ⊆ f2), updateall f1 g ⊆ updateall f2 g.
Proof.
  unfold pfsub, updateall. intros. destruct (g x).
    assumption.
    apply SS. assumption.
Qed.

(* Frame property: Updating variable x does not affect the value of any other variable z. *)
Theorem update_frame {A B} {_: EqDec A}:
  forall (s:A->B) x y z (NE: z<>x),
  update s x y z = s z.
Proof.
  intros. unfold update. destruct (z == x).
    exfalso. apply NE. assumption.
    reflexivity.
Qed.

(* Updating x and then reading it returns its new value. *)
Theorem update_updated {A B} {_: EqDec A}:
  forall (s:A->B) x y,
  update s x y x = y.
Proof.
  intros. unfold update. vreflexivity x. reflexivity.
Qed.

(* Reversing the order of assignments to two different variables yields the same store. *)
Theorem update_swap {A B} {_: EqDec A}:
  forall (s:A->B) x1 x2 y1 y2 (NE:x1<>x2),
  update (update s x1 y1) x2 y2 = update (update s x2 y2) x1 y1.
Proof.
  intros. extensionality z. unfold update.
  destruct (z == x2).
    subst z. vantisym x2 x1. reflexivity. intro. apply NE. symmetry. assumption.
    destruct (z == x1); reflexivity.
Qed.

(* Overwriting a store value discards the earlier update. *)
Theorem update_cancel {A B} {_: EqDec A}:
  forall (s:A->B) x y1 y2,
  update (update s x y1) x y2 = update s x y2.
Proof.
  intros. apply functional_extensionality. intro z. unfold update.
  destruct (z == x); reflexivity.
Qed.

(* Equivalent updates within a sequence of updates can be disregarded when searching
   for updates that cancel each other via update_cancel. *)
Theorem update_inner_same {A B} {_: EqDec A}:
  forall (s1 s2:A->B) x1 y1 x2 y2,
    update s1 x2 y2 = update s2 x2 y2 ->
  update (update s1 x1 y1) x2 y2 = update (update s2 x1 y1) x2 y2.
Proof.
  intros. destruct (x1 == x2).
    subst x2. do 2 rewrite update_cancel. assumption.
    rewrite (update_swap s1), (update_swap s2) by assumption. rewrite H. reflexivity.
Qed.

(* If variable v's value u is known for store s, then s[v:=u] is the same as s.
   This fact is useful for "stocking" store expressions with explicit updates that
   reveal the values of known variables, allowing tactics to use that information to
   make progress without searching the rest of the proof context. *)
Theorem store_upd_eq {A B} {_: EqDec A}:
  forall (s: A -> B) v u (SV: s v = u),
  s = update s v u.
Proof.
  intros.
  extensionality v0.
  destruct (v0 == v).
    subst v0. rewrite update_updated. exact SV.
    rewrite update_frame. reflexivity. assumption.
Qed.


Section Functional_choice.

Definition fchoose {A B} (f:A->bool) (g h:A->B) (x:A) :=
  if f x then h x else g x.

Theorem fchoose_comm:
  forall {A B} f (g h:A->B), fchoose f g h = fchoose (Basics.compose negb f) h g.
Proof.
  intros. extensionality x. unfold fchoose, Basics.compose. destruct (f x); reflexivity.
Qed.

Theorem fchoose_sup_l:
  forall {A B} f1 f2 (g h:A->B), (forall x, Bool.le (f1 x) (f2 x)) ->
  fchoose f1 (fchoose f2 g h) h = fchoose f2 g h.
Proof.
  intros. extensionality x. specialize (H x). unfold fchoose. destruct (f1 x).
    destruct (f2 x). reflexivity. discriminate.
    reflexivity.
Qed.

Theorem fchoose_sup_r:
  forall {A B} f1 f2 (g h:A->B), (forall x, Bool.le (f2 x) (f1 x)) ->
  fchoose f1 g (fchoose f2 g h) = fchoose f2 g h.
Proof.
  intros. extensionality x. specialize (H x). unfold fchoose. destruct (f1 x).
    reflexivity.
    destruct (f2 x). discriminate. reflexivity.
Qed.

Theorem fchoose_revert:
  forall {A B} f (g h:A->B),
  fchoose f g (fchoose f h g) = g.
Proof.
  intros. extensionality v. unfold fchoose. destruct (f v); reflexivity.
Qed.

Theorem fchoose_overwrite_l:
  forall {A B} f (g h h':A->B),
  fchoose f (fchoose f g h) h' = fchoose f g h'.
Proof.
  intros. extensionality x. unfold fchoose. destruct (f x); reflexivity.
Qed.

Theorem fchoose_overwrite_r:
  forall {A B} f (g h h':A->B),
  fchoose f g (fchoose f h h') = fchoose f g h'.
Proof.
  intros. extensionality x. unfold fchoose. destruct (f x); reflexivity.
Qed.

Theorem fchoose_update_distr:
  forall {A B} {eq:EqDec A} f g h (x:A) (y:B),
  (fchoose f g h)[x:=y] = fchoose f (g[x:=y]) (h[x:=y]).
Proof.
  intros. extensionality x'. unfold fchoose. destruct (x' == x).
    subst x'. rewrite update_updated. symmetry. destruct (f x); apply update_updated.
    rewrite update_frame by assumption. symmetry. destruct (f x'); apply update_frame; assumption.
Qed.

Theorem fchoose_update_l:
  forall {A B} {eq:EqDec A} f g h (x:A) (y:B), f x = true ->
  fchoose f (g[x:=y]) h = fchoose f g h.
Proof.
  intros. unfold fchoose. extensionality x'. destruct (x' == x).
    subst x'. rewrite H. reflexivity.
    destruct (f x'). reflexivity. apply update_frame. assumption.
Qed.

Theorem fchoose_update_r:
  forall {A B} {eq:EqDec A} f g h (x:A) (y:B), f x = false ->
  fchoose f g (h[x:=y]) = fchoose f g h.
Proof.
  intros. unfold fchoose. extensionality x'. destruct (x' == x).
    subst x'. rewrite H. reflexivity.
    destruct (f x'). apply update_frame. assumption. reflexivity.
Qed.

Theorem fchoose_update_c:
  forall {A B} {eq:EqDec A} f g h (x:A) b (y:B),
  (fchoose (f[x:=b]) g h)[x:=y] = (fchoose f g h)[x:=y].
Proof.
  intros. extensionality x'. destruct (x' == x).
    subst x'. rewrite !update_updated. reflexivity.
    unfold fchoose. rewrite !update_frame by assumption. reflexivity.
Qed.

End Functional_choice.



Section NInduction.

(* Analogues of theorems about Pos.iter, but for N.iter. *)

Corollary Niter_swap:
  forall n {A} (f: A -> A) x, N.iter n f (f x) = f (N.iter n f x).
Proof. intros. destruct n. reflexivity. apply Pos.iter_swap. Qed.

Corollary Niter_succ:
  forall n {A} (f: A -> A) x, N.iter (N.succ n) f x = f (N.iter n f x).
Proof. intros. destruct n. reflexivity. apply Pos.iter_succ. Qed.

Corollary Niter_invariant:
  forall {A} (Inv: A -> Prop) f x
         (BC: Inv x) (IC: forall x (IH: Inv x), Inv (f x)),
  forall n, Inv (N.iter n f x).
Proof.
  intros. destruct n.
    exact BC.
    simpl. apply Pos.iter_invariant.
      intros. apply IC. assumption.
      exact BC.
Qed.

Corollary Niter_add:
  forall m n {A} (f: A -> A) x,
  N.iter (m+n) f x = N.iter m f (N.iter n f x).
Proof.
  intros. destruct m.
    reflexivity.
    destruct n.
      rewrite N.add_0_r. reflexivity.
      apply Pos.iter_add.
Qed.

Theorem N_bitwise_ind:
  forall (P: N -> Prop) (BC: P 0)
    (IC: forall n (IH: P (N.div2 n)), P n),
  forall n, P n.
Proof.
  intros. destruct n as [|p]. exact BC.
  induction p; apply IC; assumption.
Qed.

Theorem N_bitwise_ind2:
  forall (P: N -> N -> Prop) (BC: P 0 0)
    (IC: forall m n (IH: P (N.div2 m) (N.div2 n)), P m n),
  forall m n, P m n.
Proof.
  intros. revert m. pattern n. apply N_bitwise_ind; intros.
    pattern m. apply N_bitwise_ind.
      exact BC.
      intros. apply IC, IH.
    apply IC, IH.
Qed.

End NInduction.


(* Specialization of common binary arithmetic lemmas to modulo-power-of-2. *)
Section ModPow2.

Theorem mp2_add_l: forall m n w, (m mod 2^w + n) mod 2^w = (m + n) mod 2^w.
Proof. intros. apply N.Div0.add_mod_idemp_l. Qed.

Theorem mp2_add_r: forall m n w, (m + n mod 2^w) mod 2^w = (m + n) mod 2^w.
Proof. intros. apply N.Div0.add_mod_idemp_r. Qed.

Theorem mp2_mod_same: forall w, 2^w mod 2^w = 0.
Proof. intros. apply N.Div0.mod_same. Qed.

Theorem mp2_mod_mod: forall n w, n mod 2^w mod 2^w = n mod 2^w.
Proof. intros. apply N.Div0.mod_mod. Qed.

Theorem N_mod_mod_pow:
  forall n a b c, a <> 0 -> n mod a^b mod a^c = n mod a^N.min b c.
Proof.
  intros. destruct (N.le_ge_cases b c) as [H1|H1].
    rewrite (N.min_l _ _ H1). eapply N.mod_small, N.lt_le_trans.
      apply N.mod_lt, N.pow_nonzero, H.
      apply N.pow_le_mono_r; assumption.
    rewrite (N.min_r _ _ H1), <- (N.sub_add _ _ H1), N.pow_add_r, N.mul_comm, N.Div0.mod_mul_r,
            N.mul_comm, N.Div0.mod_add, N.Div0.mod_mod by apply N.pow_nonzero, H. reflexivity.
Qed.

Corollary mp2_mod_mod_min:
  forall n w1 w2, n mod 2^w1 mod 2^w2 = n mod 2^N.min w1 w2.
Proof. intros. apply N_mod_mod_pow. discriminate 1. Qed.

Theorem mp2_mod_lt: forall n w, n mod 2^w < 2^w.
Proof. intros. apply N.mod_lt, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_mod_le: forall n w, n mod 2^w <= n.
Proof. intros. apply N.Div0.mod_le. Qed.

Theorem mp2_mod_mul: forall n w, (n * 2^w) mod 2^w = 0.
Proof. intros. apply N.Div0.mod_mul. Qed.

Theorem mp2_div_0_l: forall w, 0 / 2^w = 0.
Proof. intros. apply N.Div0.div_0_l. Qed.

Theorem mp2_mod_0_l: forall w, 0 mod 2^w = 0.
Proof. intros. apply N.Div0.mod_0_l. Qed.

Theorem mp2_succ_pred: forall w, N.succ (N.pred (2^w)) = 2^w.
Proof. intros. apply N.succ_pred, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_div_mul: forall n w, n * 2^w / 2^w = n.
Proof. intros. apply N.div_mul, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_div_same: forall w, 2^w / 2^w = 1.
Proof. intros. apply N.div_same, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_mul_div_le: forall n w, 2^w * (n / 2^w) <= n.
Proof. intros. apply N.Div0.mul_div_le. Qed.

Theorem mp2_div_mul_le: forall m n w, m * (n / 2^w) <= m * n / 2^w.
Proof. intros. apply N.Div0.div_mul_le. Qed.

Theorem mp2_mul_r: forall m n w, (m * (n mod 2^w)) mod 2^w = (m * n) mod 2^w.
Proof. intros. apply N.Div0.mul_mod_idemp_r. Qed.

Theorem mp2_mod_add: forall m n w, (m + n * 2^w) mod 2^w = m mod 2^w.
Proof. intros. apply N.Div0.mod_add. Qed.

Theorem mp2_mul_l: forall m n w, (m mod 2^w * n) mod 2^w = (m * n) mod 2^w.
Proof. intros. apply N.Div0.mul_mod_idemp_l. Qed.

Theorem mp2_div_mod: forall n w, n = 2^w * (n / 2^w) + n mod 2^w.
Proof. intros. apply N.Div0.div_mod. Qed.

Theorem mp2_mod_eq: forall n w, n mod 2^w = n - 2^w * (n / 2^w).
Proof. intros. apply N.Div0.mod_eq. Qed.

Theorem mp2_div_add: forall m n w, (m + n * 2^w) / 2^w = m / 2^w + n.
Proof. intros. apply N.div_add, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_div_add_l: forall m n w, (m * 2^w + n) / 2^w = m + n / 2^w.
Proof. intros. apply N.div_add_l, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_add_mod: forall m n w, (m + n) mod 2^w = (m mod 2^w + n mod 2^w) mod 2^w.
Proof. intros. apply N.Div0.add_mod. Qed.

Theorem mp2_mul_mod: forall m n w, (m * n) mod 2^w = (m mod 2^w * (n mod 2^w)) mod 2^w.
Proof. intros. apply N.Div0.mul_mod. Qed.

Theorem mp2_gt_0: forall w, 0 < 2^w.
Proof. intros. apply N.neq_0_lt_0, N.pow_nonzero. discriminate 1. Qed.

Theorem mp2_div_le_mono: forall m n w, m <= n -> m / 2^w <= n / 2^w.
Proof. intros m n w. apply N.Div0.div_le_mono. Qed.

Theorem mp2_div_mul_cancel: forall n w w', 2^w * n / (2^(w+w')) = n / 2^w'.
Proof.
  intros. rewrite N.pow_add_r.
  apply N.Div0.div_mul_cancel_l, N.pow_nonzero; discriminate 1.
Qed.

Theorem mp2_div_div: forall n w1 w2, n / 2^w1 / 2^w2 = n / 2^(w1+w2).
Proof.
  intros. rewrite N.pow_add_r.
  apply N.Div0.div_div; apply N.pow_nonzero; discriminate 1.
Qed.

Theorem mp2_div_exact: forall n w, n = 2^w * (n / 2^w) <-> n mod 2^w = 0.
Proof. intros. apply N.Div0.div_exact. Qed.

Theorem mp2_mod_divides: forall n w, n mod 2^w = 0 <-> exists m, n = 2^w * m.
Proof. intros. apply N.Div0.mod_divides. Qed.

Theorem mp2_pow_div_l: forall m n w, m mod 2^w = 0 -> (m / 2^w) ^ n = m ^ n / 2^(w*n).
Proof.
  intros m n w. rewrite N.pow_mul_r.
  apply N.pow_div_l, N.pow_nonzero. discriminate 1.
Qed.

Theorem mp2_mod_mul_r: forall n w1 w2, n mod (2^(w1+w2)) = n mod 2^w1 + 2^w1 * ((n / 2^w1) mod 2^w2).
Proof. intros. rewrite N.pow_add_r. apply N.Div0.mod_mul_r. Qed.

Theorem add_mod_same_l:
  forall w n, (2^w + n) mod 2^w = n mod 2^w.
Proof.
  intros.
  rewrite <- mp2_add_l, mp2_mod_same, N.add_0_l.
  reflexivity.
Qed.

Theorem mod_sub_add:
  forall w n m, n < 2^w -> (2^w + m - n + n) mod 2^w = m mod 2^w.
Proof.
  intros. rewrite N.sub_add.
    apply add_mod_same_l.
    eapply N.lt_le_incl, N.lt_le_trans. eassumption. apply N.le_add_r.
Qed.

Theorem N_ones_spec_ltb:
  forall m n, N.testbit (N.ones m) n = (n <? m).
Proof.
  intros. destruct (_ <? _) eqn:H.
    apply N.ones_spec_low, N.ltb_lt, H.
    apply N.ones_spec_high, N.ltb_ge, H.
Qed.

Theorem ldiff_sub:
  forall x y, N.ldiff x y = x - (N.land x y).
Proof.
  intros. rewrite N.sub_nocarry_ldiff; apply N.bits_inj; intro n;
  rewrite 2?N.ldiff_spec, N.land_spec, 1?N.bits_0;
  repeat destruct (N.testbit _ _); reflexivity.
Qed.

Theorem lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  intros. rewrite <- N.lxor_lor, N.add_nocarry_lxor by assumption. reflexivity.
Qed.

(* (a & b) ^ c = (a ^ c) & b whenever b & c = c *)
Lemma lxor_land:
  forall a b c, N.land b c = c -> N.lxor (N.land a b) c = N.land (N.lxor a c) b.
Proof.
  intros. apply N.bits_inj. apply N.bits_inj_iff in H. intro n. specialize (H n).
  do 2 rewrite N.land_spec, N.lxor_spec. rewrite <- H, N.land_spec.
  repeat destruct (N.testbit _ n); reflexivity.
Qed.

End ModPow2.


(* Theory of bit-extraction. *)
Section XBits.

Theorem shiftr_mod_xbits:
  forall n i k, N.shiftr n i mod 2^k = xbits n i (i+k).
Proof.
  intros. unfold xbits. rewrite N.add_comm. rewrite N.add_sub. reflexivity.
Qed.

Theorem xbits_spec:
  forall n i j b, N.testbit (xbits n i j) b = andb (N.testbit n (b + i)) (b + i <? j).
Proof.
  intros. unfold xbits.
  rewrite <- N.land_ones, N.land_spec, N.shiftr_spec', N_ones_spec_ltb.
  apply f_equal. destruct (b + i <? j) eqn:H.
    apply N.ltb_lt, N.lt_add_lt_sub_r, N.ltb_lt, H.
    apply N.ltb_ge, N.le_sub_le_add_r, N.ltb_ge, H.
Qed.

Theorem testbit_xbits:
  forall n i, N.testbit n i = N.odd (xbits n i (N.succ i)).
Proof.
  intros. unfold xbits.
  rewrite N.testbit_odd, N.sub_succ_l, N.sub_diag by reflexivity.
  rewrite <- N.bit0_mod, N.bit0_odd.
  destruct N.odd; reflexivity.
Qed.

Theorem xbits_equiv:
  forall n i j, xbits n i j = N.shiftr (n mod 2^j) i.
Proof.
  intros. rewrite <- N.land_ones. apply N.bits_inj. intro b.
  rewrite xbits_spec, N.shiftr_spec', N.land_spec, N_ones_spec_ltb.
  reflexivity.
Qed.

Theorem xbits_0_l:
  forall i j, xbits 0 i j = 0.
Proof.
  intros. unfold xbits. rewrite N.shiftr_0_l. reflexivity.
Qed.

Theorem xbits_0_i:
  forall n j, xbits n 0 j = n mod 2^j.
Proof.
  intros. unfold xbits. rewrite N.sub_0_r, N.shiftr_0_r. reflexivity.
Qed.

Theorem xbits_0_j:
  forall n i, xbits n i 0 = 0.
Proof.
  intros. unfold xbits. rewrite N.sub_0_l. apply N.mod_1_r.
Qed.

Lemma xbits_none:
  forall n i j, j <= i -> xbits n i j = 0.
Proof.
  intros. unfold xbits. rewrite (proj2 (N.sub_0_le _ _) H). apply N.mod_1_r.
Qed.

Theorem xbits_high:
  forall w w' n, n < 2^w -> xbits n (w - w') w = N.shiftr n (w - w').
Proof.
  intros. unfold xbits. apply N.mod_small, (N.mul_lt_mono_pos_r (2^(w-w'))).
    apply mp2_gt_0.
    rewrite <- N.pow_add_r, N.sub_add by apply N.le_sub_l. eapply N.le_lt_trans.
      rewrite N.shiftr_div_pow2, N.mul_comm. apply mp2_mul_div_le.
      exact H.
Qed.

Corollary cast_low_xbits:
  forall w w' n, cast CAST_LOW w w' n = xbits n 0 w'.
Proof. symmetry. apply xbits_0_i. Qed.

Corollary cast_high_xbits:
  forall w w' n, n < 2^w -> cast CAST_HIGH w w' n = xbits n (w - w') w.
Proof. symmetry. apply xbits_high, H. Qed.

Theorem xbits_bound:
  forall n i j, xbits n i j < 2^(j-i).
Proof.
  intros. unfold xbits. apply mp2_mod_lt.
Qed.

Theorem xbits_le:
  forall n i j, xbits n i j <= n / 2^i.
Proof.
  intros. rewrite xbits_equiv, N.shiftr_div_pow2. apply mp2_div_le_mono, mp2_mod_le.
Qed.

Theorem xbits_split:
  forall i j k n, i <= j -> j <= k -> xbits n i k = N.lor (xbits n i j) (N.shiftl (xbits n j k) (j - i)).
Proof.
  intros. unfold xbits. rewrite <- !N.land_ones.
  rewrite <- !N.ones_div_pow2, <- !N.shiftr_div_pow2 by repeat (eassumption + etransitivity).
  rewrite <- !N.shiftr_shiftl_l by assumption.
  rewrite <- !N.shiftr_land, <- N.shiftr_lor, <- N.ldiff_ones_r.
  replace (N.land n (N.ones j)) with (N.land (N.land n (N.ones k)) (N.ones j)).
    rewrite N.lor_comm, N.lor_ldiff_and. reflexivity.
    rewrite <- N.land_assoc. apply f_equal. rewrite N.land_comm, N.land_ones.
      apply N.mod_small, N.succ_lt_mono. rewrite N.ones_equiv, mp2_succ_pred.
      apply N.lt_succ_r, N.pow_le_mono_r. discriminate. assumption.
Qed.

Corollary xbits_split_0:
  forall n i j,
  xbits n 0 (i+j) = N.lor (n mod 2^i) (N.shiftl (N.shiftr n i mod 2^j) i).
Proof.
  intros.
  rewrite <- xbits_0_i.
  rewrite <- (N.add_sub j i) at 2.
  change (N.shiftr _ _ mod _) with (xbits n i (j+i)).
  rewrite (N.add_comm j). rewrite <- (N.sub_0_r i) at 5.
  apply xbits_split. apply N.le_0_l. apply N.le_add_r.
Qed.

Theorem xbits_ones:
  forall n i j, xbits (N.ones n) i j = N.ones ((N.min n j) - i).
Proof.
  symmetry. apply N.bits_inj. intro b.
  rewrite xbits_spec, !N_ones_spec_ltb, <- N.sub_min_distr_r.
  destruct (b + i <? j) eqn:H1.
    destruct (b + i <? n) eqn:H2.
      apply N.ltb_lt, N.min_glb_lt; apply N.lt_add_lt_sub_r, N.ltb_lt; assumption.
      apply N.ltb_ge, N.min_le_iff. left. apply N.le_sub_le_add_r, N.ltb_ge, H2.
    rewrite Bool.andb_false_r. apply N.ltb_ge, N.min_le_iff. right. apply N.le_sub_le_add_r, N.ltb_ge, H1.
Qed.

Theorem xbits_land:
  forall n m i j, xbits (N.land n m) i j = N.land (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.land_spec, !xbits_spec, N.land_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lor:
  forall n m i j, xbits (N.lor n m) i j = N.lor (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lor_spec, !xbits_spec, N.lor_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lxor:
  forall n m i j, xbits (N.lxor n m) i j = N.lxor (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lxor_spec, !xbits_spec, N.lxor_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_ldiff:
  forall n m i j, xbits (N.ldiff n m) i j = N.ldiff (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.ldiff_spec, !xbits_spec, N.ldiff_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lnot:
  forall a n i j, xbits (N.lnot a n) i j = N.lnot (xbits a i j) (N.min n j - i).
Proof.
  intros. unfold N.lnot. rewrite xbits_lxor, xbits_ones. reflexivity.
Qed.

Theorem xbits_shiftl:
  forall n k i j, xbits (N.shiftl n k) i j = N.shiftl (xbits n (i-k) (j-k)) (k-i).
Proof.
  intros. unfold xbits. rewrite <- !N.land_ones. destruct (N.le_ge_cases k i).
    rewrite N.shiftr_shiftl_r, <- N.sub_add_distr, N.add_sub_assoc, N.add_comm, N.add_sub,
            (proj2 (N.sub_0_le k i) H), N.shiftl_0_r by assumption. reflexivity.

    rewrite (proj2 (N.sub_0_le i k) H), N.shiftr_0_r, N.sub_0_r, N.shiftr_shiftl_l by assumption.
    destruct (N.le_ge_cases k j).

      etransitivity; [|apply N.lor_0_r].
      erewrite N.shiftl_land, <- mp2_mod_mul.
      rewrite <- N.land_ones, <- N.shiftl_mul_pow2, <- N.land_lor_distr_r.
      rewrite <- N.lxor_lor, <- N.add_nocarry_lxor by
        (rewrite N.land_ones, N.shiftl_mul_pow2; apply mp2_mod_mul).
      rewrite (N.shiftl_mul_pow2 (N.ones _)), N.mul_comm, <- N.ones_add, N.add_comm.
      rewrite N.add_sub_assoc, N.sub_add by assumption. reflexivity.

      rewrite (proj2 (N.sub_0_le j k) H0), N.land_0_r, N.shiftl_0_l. destruct (N.le_ge_cases i j).
        rewrite N.shiftl_mul_pow2, N.land_ones, <- (N.sub_add j k), <- N.add_sub_assoc, N.pow_add_r,
                N.mul_assoc by assumption. apply mp2_mod_mul.
        rewrite (proj2 (N.sub_0_le j i)) by assumption. apply N.land_0_r.
Qed.

Theorem xbits_shiftr:
  forall n k i j, xbits (N.shiftr n k) i j = xbits n (i+k) (j+k).
Proof.
  intros. unfold xbits.
  rewrite N.shiftr_shiftr, (N.add_comm i k), N.sub_add_distr, N.add_sub.
  reflexivity.
Qed.

Theorem xbits_above:
  forall n i j, n < 2^i -> xbits n i j = 0.
Proof.
  intros. destruct n as [|n]. apply xbits_0_l.
  unfold xbits. rewrite N.shiftr_eq_0.
    apply mp2_mod_0_l.
    apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

Theorem xbits_mod:
  forall n i j k, xbits (n mod 2^(i+k)) i j = xbits n i j mod 2^k.
Proof.
  intros.
  destruct (N.le_ge_cases j i). rewrite !xbits_none by assumption. reflexivity.
  rewrite xbits_equiv. unfold xbits.
  rewrite !mp2_mod_mod_min, <- !N.land_ones.
  apply N.bits_inj. intro b.
  rewrite N.land_spec, !N.shiftr_spec', N.land_spec.
  apply f_equal. rewrite !N_ones_spec_ltb.
  destruct (_<?_) eqn:H'; symmetry.
    eapply N.ltb_lt, N.add_lt_mono_r, N.lt_le_trans.
      apply N.ltb_lt, H'.
      rewrite <- (N.add_sub k i) at 2. rewrite N.sub_min_distr_r, N.add_comm, N.min_comm. apply N.sub_add_le.
    eapply N.ltb_ge, N.add_le_mono_r.
      rewrite <- N.add_min_distr_r, N.min_comm, N.add_comm, (N.sub_add _ _ H).
      apply N.ltb_ge, H'.
Qed.

Theorem xbits_below:
  forall n i j, n mod 2^j = 0 -> xbits n i j = 0.
Proof.
  intros. rewrite xbits_equiv, H. apply N.shiftr_0_l.
Qed.

Theorem fold_cbits:
  forall n1 i n2, N.lor (N.shiftl n1 i) n2 = cbits n1 i n2.
Proof. reflexivity. Qed.

Theorem fold_cbits':
  forall n1 i n2, N.lor n1 (N.shiftl n2 i) = cbits n2 i n1.
Proof. intros. rewrite N.lor_comm. reflexivity. Qed.

Theorem cbits_0_l:
  forall i n2, cbits 0 i n2 = n2.
Proof. intros. unfold cbits. rewrite N.shiftl_0_l. apply N.lor_0_l. Qed.

Theorem cbits_0_r:
  forall n1 i, cbits n1 i 0 = N.shiftl n1 i.
Proof. intros. unfold cbits. apply N.lor_0_r. Qed.

Theorem cbits_0_i:
  forall n1 n2, cbits n1 0 n2 = N.lor n1 n2.
Proof. intros. unfold cbits. rewrite N.shiftl_0_r. reflexivity. Qed.

Theorem cbits_mod:
  forall n1 n2 i, n2 < 2^i -> (cbits n1 i n2) mod 2^i = n2.
Proof.
  intros. unfold cbits. rewrite <- N.land_ones. rewrite N.land_lor_distr_l.
  replace (N.land _ _) with 0.
    rewrite N.lor_0_l, N.land_ones. apply N.mod_small, H.
    symmetry. apply N.bits_inj_0. intro k. rewrite N.land_spec. destruct (N.le_gt_cases i k).
      rewrite N.ones_spec_high by assumption. apply Bool.andb_false_r.
      rewrite N.shiftl_spec_low by assumption. reflexivity.
Qed.

Theorem xbits_cbits_lo:
  forall n1 n2 i, n2 < 2^i -> xbits (cbits n1 i n2) 0 i = n2.
Proof.
  intros. rewrite xbits_0_i. apply cbits_mod. assumption.
Qed.

Theorem xbits_cbits_hi:
  forall n1 n2 i j, n2 < 2^i -> xbits (cbits n1 i n2) i j = n1 mod 2^(j-i).
Proof.
  intros. unfold cbits.
  rewrite xbits_lor, xbits_shiftl, N.sub_diag, xbits_0_i, N.shiftl_0_r.
  rewrite xbits_above by assumption. apply N.lor_0_r.
Qed.

Theorem shiftr_cbits:
  forall n1 i n2, n2 < 2^i -> N.shiftr (cbits n1 i n2) i = n1.
Proof.
  intros. unfold cbits.
  rewrite N.shiftr_lor, N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r by reflexivity.
  rewrite (proj2 (N.shiftr_eq_0_iff _ _)). apply N.lor_0_r.
  destruct n2. left. reflexivity. right. split. reflexivity.
  apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

Theorem cbits_xbits:
  forall n i j, cbits (xbits n i j) i (xbits n 0 i) = n mod 2^N.max i j.
Proof.
  intros. destruct (N.le_ge_cases i j).
    unfold cbits. rewrite N.lor_comm. rewrite <- (N.sub_0_r i) at 3. rewrite <- xbits_split.
      rewrite N.max_r by assumption. apply xbits_0_i.
      apply N.le_0_l.
      assumption.
    rewrite xbits_none, N.max_l, xbits_0_i by assumption. apply cbits_0_l.
Qed.

Lemma N2Z_inj_ones:
  forall n, Z.of_N (N.ones n) = Z.ones (Z.of_N n).
Proof.
  intros. rewrite N.ones_equiv, Z.ones_equiv, N2Z.inj_pred, N2Z.inj_pow. reflexivity.
  apply mp2_gt_0.
Qed.

Lemma Z2N_inj_ones:
  forall z, Z.to_N (Z.ones z) = N.ones (Z.to_N z).
Proof.
  intros. rewrite Z.ones_equiv, N.ones_equiv, Z2N.inj_pred. destruct z as [|p|p]; try reflexivity.
  rewrite Z2N.inj_pow by discriminate 1. reflexivity.
Qed.

Lemma Z2N_inj_mul:
  forall z1 z2, (0 <= z1 \/ 0 <= z2 -> Z.to_N (z1 * z2) = (Z.to_N z1 * Z.to_N z2)%N)%Z.
Proof.
  assert (THM: forall m n, (0 <= m -> Z.to_N (m * n) = (Z.to_N m * Z.to_N n)%N)%Z).
    intros. destruct n.
      rewrite Z.mul_0_r, N.mul_0_r. reflexivity.
      apply Z2N.inj_mul. assumption. discriminate.
      rewrite N.mul_0_r, Z.mul_comm. destruct m; try reflexivity. exfalso. apply H. reflexivity.
  intros. destruct H.
    apply THM, H.
    rewrite Z.mul_comm, N.mul_comm. apply THM, H.
Qed.

Lemma N2Z_inj_land:
  forall n1 n2, Z.of_N (N.land n1 n2) = Z.land (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.land_spec, !Z.testbit_of_N' by assumption. apply N.land_spec.
Qed.

Lemma Z2N_inj_land:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.land z1 z2) = N.land (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id.
Qed.

Lemma N2Z_inj_lor:
  forall n1 n2, Z.of_N (N.lor n1 n2) = Z.lor (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.lor_spec, !Z.testbit_of_N' by assumption. apply N.lor_spec.
Qed.

Lemma Z2N_inj_lor:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.lor z1 z2) = N.lor (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; reflexivity + contradiction.
Qed.

Lemma N2Z_inj_lxor:
  forall n1 n2, Z.of_N (N.lxor n1 n2) = Z.lxor (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.lxor_spec, !Z.testbit_of_N' by assumption. apply N.lxor_spec.
Qed.

Lemma Z2N_inj_lxor:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.lxor z1 z2) = N.lxor (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id. 
Qed.

Lemma N2Z_inj_ldiff:
  forall n1 n2, Z.of_N (N.ldiff n1 n2) = Z.ldiff (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.ldiff_spec, !Z.testbit_of_N' by assumption. apply N.ldiff_spec.
Qed.

Lemma Z2N_inj_ldiff:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.ldiff z1 z2) = N.ldiff (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id. 
Qed.

Lemma N2Z_inj_shiftl:
  forall n1 n2, Z.of_N (N.shiftl n1 n2) = Z.shiftl (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. rewrite N.shiftl_mul_pow2, Z.shiftl_mul_pow2 by apply N2Z.is_nonneg.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply N2Z.inj_mul.
Qed.

Lemma Z2N_inj_shiftl:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.shiftl z1 z2) = N.shiftl (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1.
    rewrite Z.shiftl_0_l. reflexivity.
    destruct z2.
      reflexivity.
      simpl. erewrite (Pos.iter_swap_gen _ _ Z.to_N _ (N.mul 2)), (Pos.iter_swap_gen _ _ N.pos).
        reflexivity.
        reflexivity.
        intro a. destruct a; reflexivity.
      contradiction.
    contradiction.
Qed.

Lemma N2Z_inj_shiftr: forall n1 n2, Z.of_N (N.shiftr n1 n2) = Z.shiftr (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. rewrite N.shiftr_div_pow2, Z.shiftr_div_pow2 by apply N2Z.is_nonneg.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply N2Z.inj_div.
Qed.

Lemma Z2N_inj_shiftr:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.shiftr z1 z2) = N.shiftr (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1.
    rewrite Z.shiftr_0_l, N.shiftr_0_l. reflexivity.
    destruct z2.
      reflexivity.
      unfold Z.shiftr. simpl. erewrite (Pos.iter_swap_gen _ _ Z.to_N _ N.div2).
        reflexivity.
        exact Z2N.inj_div2.
      contradiction.
    contradiction.
Qed.

Lemma N2Z_inj_eqb:
  forall n1 n2, (n1 =? n2)%N = (Z.of_N n1 =? Z.of_N n2)%Z.
Proof.
  intros. rewrite N.eqb_compare, Z.eqb_compare, N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_eqb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> z1 =? z2 = (Z.to_N z1 =? Z.to_N z2)%N)%Z.
Proof.
  intros. rewrite N.eqb_compare, Z.eqb_compare, Z2N.inj_compare by assumption. reflexivity.
Qed.

Lemma N2Z_inj_ltb:
  forall n1 n2, (Z.of_N n1 <? Z.of_N n2)%Z = (n1 <? n2)%N.
Proof.
  intros. unfold Z.ltb. rewrite N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_ltb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> (Z.to_N z1 <? Z.to_N z2)%N = (z1 <? z2))%Z.
Proof.
  intros. unfold N.ltb. rewrite Z2N.inj_compare by assumption. reflexivity.
Qed.

Lemma N2Z_inj_leb:
  forall m n, (Z.of_N m <=? Z.of_N n)%Z = (m <=? n).
Proof.
  intros. unfold Z.leb. rewrite N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_leb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> (Z.to_N z1 <=? Z.to_N z2)%N = (z1 <=? z2))%Z.
Proof.
  intros. unfold N.leb. rewrite Z2N.inj_compare by assumption. reflexivity.
Qed.

Definition Z_xbits z i j := ((Z.shiftr z i) mod 2^Z.max 0 (j - i))%Z.

Theorem Z_xbits_spec:
  forall z i j b, (Z.testbit (Z_xbits z i j) b = Z.testbit z (b + i) && (b + i <? j) && (0 <=? b))%Z%bool.
Proof.
  intros. destruct (Z.le_gt_cases 0 b).

  unfold Z_xbits.
  rewrite <- Z.land_ones by apply Z.le_max_l.
  rewrite Z.land_spec, Z.shiftr_spec by assumption.
  rewrite Z.testbit_ones by apply Z.le_max_l.
  rewrite <- Bool.andb_assoc, (Bool.andb_comm (_ <? _)%Z).
  apply f_equal, f_equal. destruct (b + i <? j)%Z eqn:H1.
    apply Z.ltb_lt, Z.max_lt_iff. right. apply Z.lt_add_lt_sub_r, Z.ltb_lt, H1.
    apply Z.ltb_ge, Z.max_lub. assumption. apply Z.le_sub_le_add_r, Z.ltb_ge, H1.

  rewrite Z.testbit_neg_r by assumption.
  symmetry. apply Bool.andb_false_intro2, Z.leb_gt, H.
Qed.

Theorem Z_xbits_nonneg:
  forall z i j, (0 <= Z_xbits z i j)%Z.
Proof.
  intros. unfold Z_xbits. apply Z.mod_pos_bound, Z.pow_pos_nonneg.
    reflexivity.
    apply Z.le_max_l.
Qed.

Theorem Z_xbits_0_l:
  forall i j, Z_xbits 0 i j = Z0.
Proof.
  intros. unfold Z_xbits. rewrite Z.shiftr_0_l. apply Z.mod_0_l, Z.pow_nonzero.
    discriminate 1.
    apply Z.le_max_l.
Qed.

Theorem N2Z_xbits:
  forall n i j, Z.of_N (xbits n i j) = Z_xbits (Z.of_N n) (Z.of_N i) (Z.of_N j).
Proof.
  intros. unfold xbits, Z_xbits.
  rewrite N2Z.inj_mod, N2Z_inj_shiftr, N2Z.inj_pow, N2Z.inj_sub_max.
  reflexivity.
Qed.

Theorem Z2N_xbits:
  forall n i j, (0 <= n -> 0 <= i -> 0 <= j ->
  Z.to_N (Z_xbits n i j) = xbits (Z.to_N n) (Z.to_N i) (Z.to_N j))%Z.
Proof.
  intros. apply N2Z.inj. rewrite N2Z_xbits, !Z2N.id; try assumption.
    reflexivity.
    apply Z_xbits_nonneg.
Qed.

Theorem Z_xbits_equiv:
  forall z i j, Z_xbits z i j =  Z.shiftr (z mod 2^Z.max 0 j) i.
Proof.
  intros. apply Z.bits_inj. intro b. rewrite Z_xbits_spec, <- Z.land_ones by apply Z.le_max_l. destruct (Z.le_gt_cases 0 b).
    rewrite Z.shiftr_spec, Z.land_spec, (proj2 (Z.leb_le 0 b)), Bool.andb_true_r by assumption. destruct (Z.le_gt_cases 0 (b+i)).
      destruct (Z.le_ge_cases 0 j).
        rewrite Z.max_r, Z.testbit_ones, Zle_imp_le_bool by assumption. reflexivity.
        rewrite Z.max_l, Z.testbit_0_l, (proj2 (Z.ltb_ge _ _)). reflexivity.
          transitivity Z0; assumption.
          assumption.
      rewrite Z.testbit_neg_r by assumption. reflexivity.
    rewrite (proj2 (Z.leb_gt _ _)), Bool.andb_false_r, Z.testbit_neg_r by assumption. reflexivity.
Qed.

Theorem xbits_Z2N:
  forall z i j, (0 <= z)%Z -> xbits (Z.to_N z) i j = Z.to_N (Z_xbits z (Z.of_N i) (Z.of_N j)).
Proof.
  intros. rewrite Z2N_xbits, !N2Z.id. reflexivity.
    assumption.
    apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
Qed.

End XBits.



Section TwosComplement.

(* Reinterpreting an unsigned nat as a signed integer in two's complement form
   always yields an integer in range [-2^w, 2^w), where w is one less than the
   bitwidth of the original unsigned number. *)

Remark N2Z_pow2_pos:
  forall w, (0 < Z.of_N (2^w))%Z.
Proof. intros. rewrite N2Z.inj_pow. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg. Qed.

Remark N2Z_pow2_nonzero:
  forall w, Z.of_N (2^w) <> Z0.
Proof. intros. apply Z.neq_sym, Z.lt_neq, N2Z_pow2_pos. Qed.

Lemma hibits_zero_bound:
  forall n w,
    (forall b, w<=b -> N.testbit n b = false) ->
  n < 2^w.
Proof.
  intros.
  destruct n. destruct (2^w) eqn:H1. apply N.pow_nonzero in H1. contradict H1. discriminate 1. reflexivity.
  apply N.compare_nge_iff. intro P.
    apply N.log2_le_pow2 in P; [|reflexivity].
    apply H in P. rewrite N.bit_log2 in P. discriminate P. discriminate 1.
Qed.

Lemma bound_hibits_zero:
  forall w n b, n < 2^w -> w<=b -> N.testbit n b = false.
Proof.
  intros. destruct n. reflexivity. apply N.bits_above_log2, N.log2_lt_pow2. reflexivity.
  eapply N.lt_le_trans. eassumption.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Lemma Z_mod_mod_pow:
  forall z a b c, (0 < a -> 0 <= b -> 0 <= c -> z mod a^b mod a^c = z mod a^Z.min b c)%Z.
Proof.
  intros. destruct (Z.le_ge_cases b c).
    rewrite Z.min_l by assumption. apply Z.mod_small. split.
      apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; assumption.
      eapply Z.lt_le_trans.
        apply Z.mod_pos_bound, Z.pow_pos_nonneg; assumption.
        apply Z.pow_le_mono_r; assumption.
    rewrite Z.min_r, <- (Zplus_minus c b), Z.pow_add_r, Z.rem_mul_r, Z.mul_comm, Z_mod_plus_full. apply Zmod_mod.
      apply Z.pow_nonzero. apply not_eq_sym, Z.lt_neq. assumption. assumption.
      apply Z.pow_pos_nonneg. assumption. apply Z.le_0_sub. assumption.
      assumption.
      apply Z.le_0_sub. assumption.
      assumption.
Qed.

Corollary Z_mod_mod_pow2:
  forall z w1 w2, (0 <= w1 -> 0 <= w2 -> z mod 2^w1 mod 2^w2 = z mod 2^Z.min w1 w2)%Z.
Proof.
  intros. apply Z_mod_mod_pow. reflexivity. assumption. assumption.
Qed.

Theorem N_sub_lt:
  forall m n, m <> 0 -> n <> 0 -> m - n < m.
Proof.
  intros.
  rewrite <- (N.succ_pred _ H), <- (N.succ_pred _ H0), N.sub_succ.
  apply N.lt_succ_r. apply N.le_sub_l.
Qed.

Theorem N_sub_distr:
  forall x y z, z <= y -> y <= x -> x - (y - z) = x - y + z.
Proof.
  intros.
  apply (N.add_cancel_r _ _ (y-z)).
  rewrite N.sub_add by (transitivity y; [ apply N.le_sub_l | assumption ]).
  rewrite N.add_sub_assoc by assumption.
  rewrite <- N.add_assoc, (N.add_comm z y), N.add_assoc, N.add_sub.
  symmetry. apply N.sub_add. assumption.
Qed.

Theorem N_sub_mod:
  forall a b n, n <> 0 -> b <= a ->
  (a - b) mod n = a mod n + n * N.b2n (a mod n <? b mod n) - b mod n.
Proof.
  intros.
  rewrite (N.div_mod a n), (N.div_mod b n) at 1 by assumption.
  rewrite N.sub_add_distr.
  rewrite N.add_sub_swap by (apply N.mul_le_mono_l, N.Div0.div_le_mono; assumption).
  rewrite <- N.mul_sub_distr_l, N.add_comm.
  destruct (N.eq_0_gt_0_cases (a/n - b/n)).

    assert (H2: b mod n <= a mod n).
      eapply N.add_le_mono_l. rewrite <- N.div_mod by assumption.
      etransitivity. eassumption.
      rewrite (N.div_mod a n) at 1 by assumption.
      apply N.add_le_mono_r, N.mul_le_mono_l, N.sub_0_le, H1.
    rewrite H1, (proj2 (N.ltb_ge _ _) H2), N.mod_small. reflexivity.
    eapply N.le_lt_trans. apply N.le_sub_l.
    rewrite N.mul_0_r, N.add_0_r.
    eapply N.mod_lt. assumption.

    rewrite N.mul_comm. destruct (N.le_gt_cases (b mod n) (a mod n)).

      rewrite N.add_sub_swap, N.Div0.mod_add by assumption.
      rewrite (proj2 (N.ltb_ge _ _) H2), N.mul_0_r, N.add_0_r.
      eapply N.mod_small, N.le_lt_trans. apply N.le_sub_l. apply N.mod_lt, H.

      rewrite (proj2 (N.ltb_lt _ _) H2), N.mul_1_r.
      rewrite <- (N.succ_pred (a/n-_)) by apply N.neq_sym, N.lt_neq, H1.
      rewrite N.mul_succ_l, N.add_comm, <- N.add_assoc, (N.add_comm n).
      rewrite <- N.add_sub_assoc by (rewrite N.add_comm; etransitivity;
        [apply N.lt_le_incl, N.mod_lt,H|apply N.le_add_r]).
      rewrite N.add_comm, N.Div0.mod_add by assumption.
      eapply N.mod_small, N.add_lt_mono_r. rewrite N.sub_add.
        rewrite N.add_comm. apply N.add_lt_mono_l, H2.
        rewrite <- (N.add_0_l (b mod _)). apply N.add_le_mono.
          apply N.le_0_l.
          apply N.lt_le_incl, N.mod_lt, H.
Qed.

Theorem signed_range_0_l:
  forall z, signed_range 0 z -> z = Z0.
Proof.
  intros. destruct z as [|z|z].
    reflexivity.
    apply proj2 in H. destruct z; discriminate.
    apply proj1 in H. contradiction.
Qed.

Theorem signed_range_0_r:
  forall w, signed_range w 0.
Proof.
  split.
    apply Z.opp_nonpos_nonneg, Z.pow_nonneg. discriminate.
    apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem signed_range_abs:
  forall w z (SR: signed_range w z), (Z.abs z <= 2^Z.of_N (N.pred w))%Z.
Proof.
  intros. destruct w as [|w].
    apply signed_range_0_l in SR. subst z. discriminate.
    destruct z as [|n|n].
      apply Z.pow_nonneg. discriminate.
      apply Z.lt_le_incl, SR.
      rewrite N2Z.inj_pred by reflexivity. apply Z.opp_le_mono, SR.
Qed.

Theorem signed_range_mono_l:
  forall w' w z (LE: w' <= w) (SR: signed_range w' z), signed_range w z.
Proof.
  split.
    etransitivity; [|apply SR]. apply -> Z.opp_le_mono. apply Z.pow_le_mono_r.
      reflexivity.
      apply -> Z.pred_le_mono. apply N2Z.inj_le, LE.
    eapply Z.lt_le_trans. apply SR. apply Z.pow_le_mono_r.
      reflexivity.
      apply N2Z.inj_le, N.pred_le_mono, LE.
Qed.

Theorem signed_range_mono_r:
  forall w z' z (LE: (Z.abs z < Z.abs z')%Z) (SR: signed_range w z'), signed_range w z.
Proof.
  intros. destruct w as [|w].
    contradict LE. apply signed_range_0_l in SR. subst z'. apply Z.nlt_ge, Z.abs_nonneg.
    destruct z as [|n|n].
      apply signed_range_0_r.
      split.
        etransitivity.
          apply Z.opp_nonpos_nonneg, Z.pow_nonneg. discriminate.
          discriminate.
        eapply Z.lt_le_trans.
          apply LE.
          apply signed_range_abs, SR.
      split; etransitivity.
        rewrite <- N2Z.inj_pred by reflexivity. apply -> Z.opp_le_mono. apply signed_range_abs, SR.
        apply Z.opp_le_mono. rewrite Z.opp_involutive. apply Z.lt_le_incl, LE.
        apply Zlt_neg_0.
        apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem signed_range_hibits:
  forall i w z (SR: signed_range w z) (HI: w <= i),
  Z.testbit z (Z.of_N i) = Z.testbit z (Z.pred (Z.of_N w)).
Proof.
  intros. destruct w as [|w].
    apply signed_range_0_l in SR. subst z. rewrite !Z.testbit_0_l. reflexivity.
    destruct z as [|z|z].
      rewrite !Z.testbit_0_l. reflexivity.
      replace (Z.testbit _ _) with false; symmetry; apply Z.bits_above_log2; try discriminate 1.
        apply Z.log2_lt_pow2. reflexivity. rewrite <- N2Z.inj_pred by reflexivity. apply SR.
        apply Z2N.inj_lt.
          apply Z.log2_nonneg.
          apply N2Z.is_nonneg.
          rewrite N2Z.id. eapply N.lt_le_trans; [|eassumption]. apply N.lt_pred_lt, N2Z.inj_lt. rewrite Z2N.id.
            apply Z.log2_lt_pow2. reflexivity. apply SR.
            apply Z.log2_nonneg.
      destruct (Pos.lt_total z 1) as [H|[H|H]].
        contradict H. apply Pos.nlt_1_r.
        subst z. rewrite Z.bits_m1 by apply N2Z.is_nonneg. symmetry. apply Z.bits_m1, Z.lt_le_pred. reflexivity.

        apply proj1, Z.opp_le_mono in SR. rewrite Z.opp_involutive in SR.
        replace (Z.testbit _ _) with true; symmetry; apply Z.bits_above_log2_neg; try reflexivity.
          apply Z.log2_lt_pow2.
            apply Z.succ_lt_mono. rewrite Z.succ_pred. exact H.
            apply Z.lt_pred_le. apply SR.
          apply Z2N.inj_lt.
            apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            rewrite N2Z.id. eapply N.lt_le_trans; [|eassumption]. apply N2Z.inj_lt. rewrite Z2N.id.
              apply Z.log2_lt_pow2.
                apply Z.succ_lt_mono. rewrite Z.succ_pred. exact H.
                apply Z.lt_pred_le. etransitivity. apply SR. apply Z.pow_le_mono_r. reflexivity. apply Z.le_pred_l.
              apply Z.log2_nonneg.
Qed.

Theorem hibits_signed_range:
  forall w z (HI: forall i, w <= i -> Z.testbit z (Z.of_N i) = Z.testbit z (Z.pred (Z.of_N w))),
  signed_range w z.
Proof.
  intros. destruct w as [|w].
    replace z with Z0.
      apply signed_range_0_r.
      symmetry. apply Z.bits_inj_0. intro i. destruct (Z.neg_nonneg_cases i).
        apply Z.testbit_neg_r. assumption.
        rewrite <- (Z2N.id i) by assumption. apply HI, N.le_0_l.
    split.
      apply Z.opp_le_mono, Z.lt_pred_le. rewrite Z.opp_involutive. destruct (Z.nonpos_pos_cases (Z.pred (-z))) as [H|H].
        eapply Z.le_lt_trans. exact H. apply Z.pow_pos_nonneg. reflexivity. destruct w; discriminate.
        apply Z.log2_lt_pow2. exact H. apply Z.lt_nge. intro H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
          apply Z.lt_pred_le, Z2N.inj_le in H2.
            rewrite N2Z.id in H2. assert (H3:=N.le_le_succ_r _ _ H2). apply HI in H2. apply HI in H3. rewrite <- H3, N2Z.inj_succ, !Z2N.id in H2.
              rewrite Z.bit_log2_neg, Z.bits_above_log2_neg in H2.
                discriminate.
                apply Z.opp_pos_neg. etransitivity. exact H. apply Z.lt_pred_l.
                apply Z.lt_succ_diag_r.
                apply Z.opp_lt_mono. rewrite Z.opp_involutive. apply Z.pred_lt_mono, H.
              apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            apply Z.log2_nonneg.
          rewrite H2, Z.bit_log2_neg in HI.
            specialize (HI _ (N.le_refl _)). rewrite Z.bits_above_log2_neg in HI.
              discriminate.
              apply Z.opp_pos_neg. etransitivity. exact H. apply Z.lt_pred_l.
              rewrite <- H2. apply Z.lt_pred_l.
            apply Z.opp_lt_mono. rewrite Z.opp_involutive. apply Z.pred_lt_mono, H.
      destruct (Z.nonpos_pos_cases z) as [H|H].
        eapply Z.le_lt_trans. exact H. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
        rewrite N2Z.inj_pred by reflexivity. apply Z.log2_lt_pow2. exact H. apply Z.lt_nge. intro H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
          apply Z.lt_pred_le, Z2N.inj_le in H2.
            rewrite N2Z.id in H2. assert (H3:=N.le_le_succ_r _ _ H2). apply HI in H2. apply HI in H3. rewrite <- H3, N2Z.inj_succ, !Z2N.id in H2.
              rewrite Z.bit_log2 in H2 by exact H. rewrite Z.bits_above_log2 in H2.
                discriminate.
                apply Z.lt_le_incl, H.
                apply Z.lt_succ_diag_r.
              apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            apply Z.log2_nonneg.
          rewrite H2, Z.bit_log2 in HI by exact H. specialize (HI _ (N.le_refl _)). rewrite Z.bits_above_log2 in HI.
            discriminate.
            apply Z.lt_le_incl, H.
            rewrite <- H2. apply Z.lt_pred_l.
Qed.

Theorem N2Z_ofZ:
  forall w z, Z.of_N (ofZ w z) = (z mod 2^Z.of_N w)%Z.
Proof.
  intros. unfold ofZ. rewrite Z2N.id.
    reflexivity.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_N2Z:
  forall w n, ofZ w (Z.of_N n) = n mod 2^w.
Proof.
  intros. unfold ofZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pow, <- N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  apply N2Z.id.
Qed.

Theorem ofZ_bound:
  forall w z, ofZ w z < 2^w.
Proof.
  intros. rewrite <- (N2Z.id (2^w)). unfold ofZ. apply Z2N.inj_lt.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
    rewrite N2Z.inj_pow. apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem canonicalZ_bounds:
  forall w z, signed_range w (canonicalZ (Z.of_N w) z).
Proof.
  intros. unfold canonicalZ, signed_range.
  destruct w as [|w]. rewrite Z.mod_1_r. split; reflexivity.
  rewrite N2Z.inj_pred by reflexivity.
  rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 3 6.
  set (w' := Z.pred (Z.of_N (N.pos w))).
  rewrite Z.pow_succ_r by (apply Zlt_0_le_0_pred; reflexivity).
  split.
    apply Z.le_add_le_sub_l. rewrite Z.add_opp_diag_r. apply Z.mod_pos_bound, Z.mul_pos_pos.
      reflexivity.
      apply Z.pow_pos_nonneg. reflexivity. apply Zlt_0_le_0_pred. reflexivity.
    apply Z.lt_sub_lt_add_r. rewrite Z.add_diag. apply Z.mod_pos_bound, Z.mul_pos_pos.
      reflexivity.
      apply Z.pow_pos_nonneg. reflexivity. apply Zlt_0_le_0_pred. reflexivity.
Qed.

Corollary toZ_bounds:
  forall w n, signed_range w (toZ w n).
Proof. intros. apply canonicalZ_bounds. Qed.

Corollary ofZ_0_l:
  forall z, ofZ 0 z = 0.
Proof. intro. apply N.lt_1_r, ofZ_bound. Qed.

Theorem ofZ_0_r:
  forall w, ofZ w 0 = 0.
Proof. reflexivity. Qed.

Theorem canonicalZ_neg_l:
  forall w z, (w < 0)%Z -> canonicalZ w z = z.
Proof.
  intros. unfold canonicalZ.
  rewrite (Z.pow_neg_r _ w), Zmod_0_r by assumption. apply Z.add_simpl_r.
Qed.

Theorem canonicalZ_0_l:
  forall z, canonicalZ 0 z = Z0.
Proof.
  intros. unfold canonicalZ. rewrite Z.mod_1_r. reflexivity.
Qed.

Theorem canonicalZ_0_r:
  forall w, canonicalZ w 0 = Z0.
Proof.
  intros. destruct w as [|w|w].
    reflexivity.
    unfold canonicalZ. rewrite Z.add_0_l, Z.mod_small. apply Z.sub_diag. split.
      apply Z.pow_nonneg. discriminate.
      apply Z.pow_lt_mono_r. reflexivity. discriminate. apply Z.lt_pred_l.
    apply canonicalZ_neg_l. reflexivity.
Qed.

Corollary toZ_0_l:
  forall n, toZ 0 n = Z0.
Proof.
  intros. assert (B:=toZ_bounds 0 n). destruct B as [B1 B2].
  destruct (toZ 0 n). reflexivity. destruct p; discriminate. contradiction.
Qed.

Corollary toZ_0_r:
  forall w, toZ w 0 = Z0.
Proof. intros. apply canonicalZ_0_r. Qed.

Corollary sbop1_0_l:
  forall zop n1 n2, sbop1 zop 0 n1 n2 = 0.
Proof. intros. apply ofZ_0_l. Qed.

Corollary sbop2_0_l:
  forall zop n1 n2, sbop2 zop 0 n1 n2 = 0.
Proof. intros. apply ofZ_0_l. Qed.

Theorem eqm_eq:
  forall w z1 z2 (SR1: signed_range w z1) (SR2: signed_range w z2),
  eqm (2^Z.of_N w) z1 z2 -> z1 = z2.
Proof.
  unfold signed_range, eqm. intros. destruct w as [|w].
    destruct SR1, SR2, z1, z2; try first [ contradiction | destruct p; discriminate ]. reflexivity.

  assert (H1: forall z, signed_range (N.pos w) z ->
      (z + 2^Z.pred (Z.of_N (N.pos w)) = (z + 2^Z.pred (Z.of_N (N.pos w))) mod 2^Z.of_N (N.pos w))%Z).
    intros. symmetry. apply Z.mod_small. split.
      apply Z.le_sub_le_add_r. rewrite Z.sub_0_l. apply H0.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 2. rewrite Z.pow_succ_r, <- Z.add_diag.
         apply Z.add_lt_mono_r. rewrite <- N2Z.inj_pred by reflexivity. apply H0.
         destruct w; discriminate.

  apply (Z.add_cancel_r _ _ (2^Z.pred (Z.of_N (N.pos w)))). etransitivity.
    apply H1, SR1.
    rewrite <- Zplus_mod_idemp_l, H, Zplus_mod_idemp_l. symmetry. apply H1, SR2.
Qed.

Theorem N2Z_eqm_eq:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
  eqm (2^Z.of_N w) (Z.of_N n1) (Z.of_N n2) -> n1 = n2.
Proof.
  unfold eqm. intros. revert H.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow, <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  intro H. apply N2Z.inj. rewrite !N.mod_small in H; assumption.
Qed.

Theorem eqm_canonicalZ:
  forall w' w z, (0 <= w' -> w' <= w -> eqm (2^w') (canonicalZ w z) z)%Z.
Proof.
  intros. unfold eqm, canonicalZ.
  rewrite <- Zminus_mod_idemp_l, Z_mod_mod_pow2.
    rewrite Z.min_r, Zminus_mod_idemp_l, Z.add_simpl_r by assumption. reflexivity.
    etransitivity; eassumption.
    assumption.
Qed.

Theorem eqm_toZ:
  forall w' w n, (0 <= w' -> w' <= Z.of_N w -> eqm (2^w') (toZ w n) (Z.of_N n))%Z.
Proof.
  intros. etransitivity. apply eqm_canonicalZ.
    assumption.
    assumption.
    reflexivity.
Qed.

Theorem eqm_ofZ:
  forall w' w z, (0 <= w' -> w' <= Z.of_N w -> eqm (2^w') (Z.of_N (ofZ w z)) z)%Z.
Proof.
  intros. unfold ofZ, eqm. rewrite Z2N.id.
    rewrite <- (Z.min_r _ _ H0) at 2. apply Z_mod_mod_pow2. apply N2Z.is_nonneg. assumption.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem canonicalZ_mod_pow2:
  forall w' w z, (0 <= w -> w <= w' -> canonicalZ w (z mod 2^w') = canonicalZ w z)%Z.
Proof.
  intros. unfold canonicalZ at 1. rewrite <- Zplus_mod_idemp_l, Z_mod_mod_pow2, (Z.min_r _ _ H0), Zplus_mod_idemp_l.
    reflexivity.
    etransitivity; eassumption.
    assumption.
Qed.

Theorem mod_pow2_canonicalZ:
  forall w w' z, (0 <= w' -> w' <= w -> (canonicalZ w z) mod 2^w' = z mod 2^w')%Z.
Proof.
  intros. apply eqm_canonicalZ; assumption.
Qed.

Theorem toZ_mod_pow2:
  forall w' w n, w <= w' -> toZ w (n mod 2^w') = toZ w n.
Proof.
  intros. unfold toZ. rewrite N2Z.inj_mod, N2Z.inj_pow.
    apply canonicalZ_mod_pow2, N2Z.inj_le, H.
    apply N2Z.is_nonneg.
Qed.

Theorem mod_pow2_toZ:
  forall w w' n, w' <= w  -> (toZ w n mod 2^Z.of_N w')%Z = Z.of_N (n mod 2^w').
Proof.
  intros. unfold toZ. rewrite mod_pow2_canonicalZ, N2Z.inj_mod, N2Z.inj_pow. reflexivity.
    apply N2Z.is_nonneg.
    apply N2Z.inj_le, H.
Qed.

Theorem ofZ_mod_pow2:
  forall w w' z, w' <= w -> ofZ w' (z mod 2^Z.of_N w) = ofZ w' z.
Proof.
  intros. unfold ofZ. rewrite Z_mod_mod_pow2, Z.min_r. reflexivity.
    apply N2Z.inj_le, H.
    apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
Qed.

Theorem mod_pow2_ofZ:
  forall w w' z, w <= w' -> ofZ w z mod 2^w' = ofZ w z.
Proof.
  intros. unfold ofZ. eapply N.mod_small, N.lt_le_trans.
    apply ofZ_bound.
    apply N.pow_le_mono_r. discriminate. assumption.
Qed.

Theorem toZ_ofZ_canonicalZ:
  forall w' w z, w' <= w -> toZ w' (ofZ w z) = canonicalZ (Z.of_N w') z.
Proof.
  intros. unfold toZ. rewrite N2Z_ofZ. apply canonicalZ_mod_pow2, N2Z.inj_le, H. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_canonicalZ:
  forall w w' z, w' <= w -> ofZ w' (canonicalZ (Z.of_N w) z) = ofZ w' z.
Proof.
  intros. unfold ofZ. rewrite mod_pow2_canonicalZ. reflexivity.
    apply N2Z.is_nonneg.
    apply N2Z.inj_le, H.
Qed.

Theorem eqm_canonicalZ_op:
  forall f w z, (forall z0, eqm (2^w) (f z0) (f (z0 mod 2^w)%Z)) -> eqm (2^w) (f z) (f (canonicalZ w z)).
Proof.
  intros. destruct (Z.lt_ge_cases w 0).
    rewrite canonicalZ_neg_l by assumption. reflexivity.
    etransitivity. apply H. rewrite <- (mod_pow2_canonicalZ w w z), <- H. reflexivity. assumption. reflexivity.
Qed.

Theorem eqm_canonicalZ_bop:
  forall f w z1 z2, (forall z z', eqm (2^w) (f z z') (f (z mod 2^w) (z' mod 2^w))%Z) ->
  eqm (2^w) (f z1 z2) (f (canonicalZ w z1) (canonicalZ w z2)).
Proof.
  intros. destruct (Z.lt_ge_cases w 0).
    rewrite !canonicalZ_neg_l by assumption. reflexivity.
    etransitivity. apply H.
      rewrite <- (mod_pow2_canonicalZ w w z1), <- (mod_pow2_canonicalZ w w z2) by solve [ assumption | reflexivity ].
      rewrite <- H. reflexivity.
Qed.

Theorem eqm_ofZ_canonicalZ:
  forall f w z, (forall z0, eqm (2^Z.of_N w) (f z0) (f (z0 mod 2^Z.of_N w)))%Z -> ofZ w (f (canonicalZ (Z.of_N w) z)) = ofZ w (f z).
Proof.
  intros. unfold ofZ. erewrite H, eqm_canonicalZ, <- H. reflexivity.
    apply N2Z.is_nonneg.
    reflexivity.
Qed.

Corollary canonicalZ_add_r:
  forall w z1 z2,
  ofZ w (z1 + canonicalZ (Z.of_N w) z2) = ofZ w (z1 + z2).
Proof.
  intros. rewrite eqm_ofZ_canonicalZ. reflexivity.
  symmetry. apply Zplus_mod_idemp_r.
Qed.

Corollary canonicalZ_add_l:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 + z2) = ofZ w (z1 + z2).
Proof.
  intros. pose (f x := (x+z2)%Z).
  change (z1 + z2)%Z with (f z1).
  change (_ + z2)%Z with (f (canonicalZ (Z.of_N w) z1)).
  apply eqm_ofZ_canonicalZ. symmetry. apply Zplus_mod_idemp_l.
Qed.

Corollary canonicalZ_add:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 + canonicalZ (Z.of_N w) z2) = ofZ w (z1 + z2).
Proof.
  intros. rewrite canonicalZ_add_l, canonicalZ_add_r. reflexivity.
Qed.

Corollary canonicalZ_sub_r:
  forall w z1 z2,
  ofZ w (z1 - canonicalZ (Z.of_N w) z2) = ofZ w (z1 - z2).
Proof.
  intros. rewrite eqm_ofZ_canonicalZ. reflexivity.
  symmetry. apply Zminus_mod_idemp_r.
Qed.

Corollary canonicalZ_sub_l:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 - z2) = ofZ w (z1 - z2).
Proof.
  intros. pose (f x := (x-z2)%Z).
  change (z1 - z2)%Z with (f z1).
  change (_ - z2)%Z with (f (canonicalZ (Z.of_N w) z1)).
  apply eqm_ofZ_canonicalZ. symmetry. apply Zminus_mod_idemp_l.
Qed.

Corollary canonicalZ_sub:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 - canonicalZ (Z.of_N w) z2) = ofZ w (z1 - z2).
Proof.
  intros. rewrite canonicalZ_sub_l, canonicalZ_sub_r. reflexivity.
Qed.

Corollary canonicalZ_mul_r:
  forall w z1 z2,
  ofZ w (z1 * canonicalZ (Z.of_N w) z2) = ofZ w (z1 * z2).
Proof.
  intros. rewrite eqm_ofZ_canonicalZ. reflexivity.
  symmetry. apply Zmult_mod_idemp_r.
Qed.

Corollary canonicalZ_mul_l:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 * z2) = ofZ w (z1 * z2).
Proof.
  intros. pose (f x := (x*z2)%Z).
  change (z1 * z2)%Z with (f z1).
  change (_ * z2)%Z with (f (canonicalZ (Z.of_N w) z1)).
  apply eqm_ofZ_canonicalZ. symmetry. apply Zmult_mod_idemp_l.
Qed.

Corollary canonicalZ_mul:
  forall w z1 z2,
  ofZ w (canonicalZ (Z.of_N w) z1 * canonicalZ (Z.of_N w) z2) = ofZ w (z1 * z2).
Proof.
  intros. rewrite canonicalZ_mul_l, canonicalZ_mul_r. reflexivity.
Qed.

Theorem canonicalZ_id:
  forall w' w z (LE: w' <= (Z.to_N w)) (SR: signed_range w' z), canonicalZ w z = z.
Proof.
  intros. destruct (Z.neg_nonneg_cases w) as [H|H].
    replace w' with 0 in SR.
      apply signed_range_0_l in SR. subst z. apply canonicalZ_0_r.
      symmetry. apply N.le_0_r. destruct w; try discriminate. exact LE.
    rewrite <- (Z2N.id w) by exact H. apply (eqm_eq (Z.to_N w)).
      apply canonicalZ_bounds.
      eapply signed_range_mono_l; eassumption.
      apply eqm_canonicalZ. apply N2Z.is_nonneg. reflexivity.
Qed.

Theorem canonicalZ_involutive:
  forall w1 w2 z, (0 <= w1 -> 0 <= w2 -> canonicalZ w1 (canonicalZ w2 z) = canonicalZ (Z.min w1 w2) z)%Z.
Proof.
  intros.
  destruct (Z.le_ge_cases w1 w2) as [H1|H1].
    rewrite (Z.min_l _ _ H1), <- (canonicalZ_mod_pow2 _ _ _ H H1), mod_pow2_canonicalZ.
      rewrite (canonicalZ_mod_pow2 _ _ _ H). reflexivity. assumption.
      assumption.
      reflexivity.
    rewrite (Z.min_r _ _ H1). apply (canonicalZ_id (Z.to_N w2)).
      apply Z2N.inj_le; assumption.
      rewrite <- (Z2N.id w2) at 2 by assumption. apply canonicalZ_bounds.
Qed.

Theorem ofZ_toZ_bitcast:
  forall w w' n, w' <= w -> ofZ w' (toZ w n) = n mod 2^w'.
Proof.
  intros. unfold ofZ. rewrite mod_pow2_toZ by exact H. apply N2Z.id.
Qed.

Corollary ofZ_toZ:
  forall w n, ofZ w (toZ w n) = n mod 2^w.
Proof. intros. apply ofZ_toZ_bitcast. reflexivity. Qed.

Theorem eqm_toZ_ofZ:
  forall w' w w0 z, w0 <= w' -> w' <= w -> eqm (2^Z.of_N w0) (toZ w' (ofZ w z)) z.
Proof.
  intros.
  rewrite toZ_ofZ_canonicalZ by assumption.
  apply eqm_canonicalZ, N2Z.inj_le.
    apply N2Z.is_nonneg.
    assumption.
Qed.

Corollary toZ_ofZ:
  forall w z (SR: signed_range w z), toZ w (ofZ w z) = z.
Proof.
  intros. rewrite toZ_ofZ_canonicalZ by reflexivity.
  eapply canonicalZ_id, SR. rewrite N2Z.id. reflexivity.
Qed.

Corollary toZ_inj:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
    toZ w n1 = toZ w n2 -> n1 = n2.
Proof.
  intros.
  erewrite <- (N.mod_small n1), <- (N.mod_small n2) by eassumption.
  rewrite <- (ofZ_toZ w n1), <- (ofZ_toZ w n2), H by assumption.
  reflexivity.
Qed.

Theorem ofZ_inj:
  forall w z1 z2 (SR1: signed_range w z1) (SR2: signed_range w z2),
    ofZ w z1 = ofZ w z2 -> z1 = z2.
Proof.
  intros. rewrite <- (toZ_ofZ w z1), <- (toZ_ofZ w z2), H by assumption. reflexivity.
Qed.

Theorem canonicalZ_toZ:
  forall w w' z, w' <= w -> canonicalZ (Z.of_N w') (toZ w z) = toZ w' z.
Proof.
  intros.
  erewrite <- toZ_ofZ_canonicalZ by eassumption.
  rewrite ofZ_toZ. apply toZ_mod_pow2. assumption.
Qed.

Theorem canonicalZ_nonneg:
  forall w z, (z mod 2^w < 2^Z.pred w -> canonicalZ w z = z mod 2^w)%Z.
Proof.
  intros. destruct (Z.lt_trichotomy w 0) as [H2|[H2|H2]].
    rewrite Z.pow_neg_r, Zmod_0_r by exact H2. apply canonicalZ_neg_l. assumption.
    subst w. rewrite Z.mod_1_r. apply canonicalZ_0_l.
    erewrite <- canonicalZ_mod_pow2; [|apply Z.lt_le_incl, H2 | reflexivity].
      unfold canonicalZ. rewrite Z.mod_small, Z.add_simpl_r. reflexivity. split.
        apply Z.add_nonneg_nonneg.
          apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply Z.lt_le_incl, H2.
          apply Z.pow_nonneg. discriminate.
        rewrite <- (Z.succ_pred w) at 3. rewrite Z.pow_succ_r, <- Z.add_diag.
          apply Z.add_lt_le_mono. assumption. reflexivity.
          apply Z.lt_le_pred, H2.
Qed.

Theorem canonicalZ_neg:
  forall w z, (0 < w -> 2^Z.pred w <= z mod 2^w -> canonicalZ w z = z mod 2^w - 2^w)%Z.
Proof.
  intros. erewrite <- canonicalZ_mod_pow2; [|apply Z.lt_le_incl, H | reflexivity]. unfold canonicalZ.
  rewrite <- (Z.sub_add (2^Z.pred w) (z mod 2^w)) at 1.
  rewrite <- Z.add_assoc, Z.add_diag, <- Z.pow_succ_r, Z.succ_pred by apply Z.lt_le_pred, H.
  rewrite <- Z.add_mod_idemp_r, Z.mod_same, Z.add_0_r by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_incl, H ]).
  rewrite Z.mod_small, <- Z.sub_add_distr, Z.add_diag.
    rewrite <- Z.pow_succ_r, Z.succ_pred by apply Z.lt_le_pred, H. reflexivity.
    split.
      apply Z.le_0_sub. assumption.
      eapply Z.le_lt_trans.
        apply Z.le_sub_nonneg, Z.pow_nonneg. discriminate.
        apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply Z.lt_le_incl, H.
Qed.

Theorem toZ_nonneg:
  forall w n, n mod 2^w < 2^N.pred w <-> toZ w n = Z.of_N (n mod 2^w).
Proof.
  split; intro H1.

    destruct w as [|w].
      rewrite N.mod_1_r. apply toZ_0_l.
      unfold toZ. rewrite canonicalZ_nonneg; change 2%Z with (Z.of_N 2); rewrite <- N2Z.inj_pow.
        symmetry. apply N2Z.inj_mod.

        rewrite <- N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
        rewrite <- N2Z.inj_pred, <- N2Z.inj_pow by reflexivity.
        apply N2Z.inj_lt, H1.

    apply (f_equal Z.to_N) in H1. rewrite N2Z.id in H1. rewrite <- H1. destruct (toZ w n) eqn:H2.
      apply mp2_gt_0.
      apply N2Z.inj_lt. rewrite Z2N.id, N2Z.inj_pow, <- H2 by discriminate. apply toZ_bounds.
      apply mp2_gt_0.
Qed.

Theorem toZ_neg:
  forall w n, 2^N.pred (N.pos w) <= n mod 2^(N.pos w) <-> toZ (N.pos w) n = (Z.of_N (n mod 2^(N.pos w)) - 2^Z.of_N (N.pos w))%Z.
Proof.
  split; intro H1.

    unfold toZ. rewrite canonicalZ_neg; change 2%Z with (Z.of_N 2); try rewrite <- N2Z.inj_pow.
      rewrite <-N2Z.inj_mod. reflexivity.
      reflexivity.
      rewrite <- N2Z.inj_pred, <- N2Z.inj_pow, <- N2Z.inj_mod.
        apply N2Z.inj_le, H1.
        reflexivity.

    apply Z.add_move_r, (f_equal Z.to_N) in H1. rewrite N2Z.id in H1. rewrite <- H1.
    rewrite <- (N2Z.id (2^_)). apply Z2N.inj_le.
      apply N2Z.is_nonneg.
      rewrite <- (Z.add_opp_diag_l (2^Z.pred (Z.of_N (N.pos w)))). apply Z.add_le_mono.
        apply toZ_bounds.
        apply Z.pow_le_mono_r. reflexivity. apply Z.le_pred_l.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))), Z.pow_succ_r, <- Z.add_diag, Z.add_assoc.
        rewrite <- (Z.add_0_l (Z.of_N _)), N2Z.inj_pow, N2Z.inj_pred.
          apply Z.add_le_mono_r, Z.le_sub_le_add_r. rewrite Z.sub_0_l. apply toZ_bounds.
          reflexivity.
        apply Z.lt_le_pred. reflexivity.
Qed.

Theorem testbit_ofZ:
  forall w z i, N.testbit (ofZ w z) i = andb (i <? w) (Z.testbit z (Z.of_N i)).
Proof.
  intros. destruct (N.lt_ge_cases i w).
    rewrite (proj2 (N.ltb_lt _ _) H). unfold ofZ. rewrite <- Z.testbit_of_N, Z2N.id.
      apply Z.mod_pow2_bits_low, N2Z.inj_lt, H.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    rewrite (proj2 (N.ltb_ge _ _) H). eapply bound_hibits_zero.
      apply ofZ_bound.
      assumption.
Qed.

Theorem testbit_canonicalZ:
  forall w z i, (0 <= w -> Z.testbit (canonicalZ w z) i = Z.testbit z (Z.min i (Z.pred w)))%Z.
Proof.
  intros. apply Z.le_lteq in H. destruct H.
    unfold canonicalZ. destruct (Z.le_gt_cases i (Z.pred w)) as [H2|H2].

      rewrite Z.min_l by assumption.
      rewrite <- (Z.mod_pow2_bits_low _ w) by apply Z.lt_le_pred, H2.
      rewrite Zminus_mod_idemp_l, Z.add_simpl_r.
      apply Z.mod_pow2_bits_low, Z.lt_le_pred, H2.

      rewrite Z.min_r by apply Z.lt_le_incl, H2.
      rewrite <- (Z.sub_add (Z.pred w) i), <- Z.div_pow2_bits; [| apply Z.lt_le_pred, H | apply Z.le_0_sub, Z.lt_le_incl, H2].
      rewrite <- Z.add_opp_r, Z.opp_eq_mul_m1, Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_pred, H ]).
      rewrite <- Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite <- Zplus_mod_idemp_l, <- !Z.land_ones, Z.shiftr_land by apply Z.lt_le_incl, H.
      rewrite Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite <- (Z.mul_1_l (2^Z.pred w)) at 1.
      rewrite Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_pred, H ]).
      rewrite <- Z.shiftr_div_pow2, Z.shiftr_land, !Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite !Z.ones_div_pow2 by (split; [ apply Z.lt_le_pred, H | apply Z.le_pred_l ]).
      rewrite Z.sub_pred_r, Z.sub_diag, (Z.land_ones (_/_) 1) by discriminate.
      rewrite <- Z.testbit_spec' by apply Z.lt_le_pred, H.
      destruct (Z.testbit z (Z.pred w)).
        apply Z.bits_m1, Z.le_0_sub, Z.lt_le_incl, H2.
        apply Z.testbit_0_l.

    subst w. rewrite canonicalZ_0_l, Z.bits_0. symmetry. apply Z.testbit_neg_r, Z.min_lt_iff.
    right. reflexivity.
Qed.

Corollary testbit_toZ:
  forall w n i, w <> 0 -> Z.testbit (toZ w n) (Z.of_N i) = N.testbit n (N.min i (N.pred w)).
Proof.
  intros. unfold toZ.
  rewrite testbit_canonicalZ, <- N2Z.inj_pred, <- N2Z.inj_min.
    apply N2Z.inj_testbit.
    apply N.neq_0_lt_0, H.
    apply N2Z.is_nonneg.
Qed.

Theorem signbit:
  forall n w, w <> 0 -> (N.testbit n (N.pred w) = (toZ w n <? 0))%Z.
Proof.
  intros. rewrite <- (N.min_id (N.pred w)). rewrite <- testbit_toZ by assumption.
  apply Z.b2z_inj. rewrite Z.testbit_spec' by apply N2Z.is_nonneg.
  destruct (_ <? 0)%Z eqn:SB.

    rewrite <- (Z.add_simpl_r (toZ w n) (2^Z.of_N (N.pred w))), <- Z.add_opp_r.
    rewrite  <- (Z.mul_1_l (2^_)) at 2.
    rewrite <- Z.mul_opp_l, Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply N2Z.is_nonneg ]).
    rewrite Z.div_small. reflexivity. split.
      apply Z.le_sub_le_add_r. rewrite Z.sub_0_l, N2Z.inj_pred by apply N.neq_0_lt_0, H. apply toZ_bounds.
      apply Z.lt_add_lt_sub_r. rewrite Z.sub_diag. apply Z.ltb_lt, SB.

    rewrite Z.div_small. reflexivity. split. apply Z.ltb_ge, SB. apply toZ_bounds.
Qed.

Theorem toZ_sign:
  forall n w, n mod 2^w < 2^N.pred w <-> (0 <= toZ w n)%Z.
Proof.
  destruct w as [|w]; split; intro H1.
    rewrite toZ_0_l. reflexivity.
    rewrite N.mod_1_r. reflexivity.
    erewrite <- toZ_mod_pow2 by reflexivity. unfold toZ, canonicalZ. rewrite Z.mod_small; [|split].
      rewrite Z.add_simpl_r. apply N2Z.is_nonneg.
      apply Z.add_nonneg_nonneg. apply N2Z.is_nonneg. apply Z.pow_nonneg. discriminate.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 2. rewrite Z.pow_succ_r, <- Z.add_diag.
        apply Z.add_lt_mono_r. rewrite <- (Z2N.id (2^_)).
          apply N2Z.inj_lt. rewrite Z2N.inj_pow.
            rewrite Z2N.inj_pred, N2Z.id. exact H1.
            discriminate.
            apply Z.lt_le_pred. reflexivity.
          apply Z.pow_nonneg. discriminate.
        apply Z.lt_le_pred. reflexivity.
    rewrite <- ofZ_toZ. unfold ofZ. rewrite Z.mod_small; [|split].
      rewrite <- N2Z.id. apply Z2N.inj_lt.
        exact H1.
        apply N2Z.is_nonneg.
        rewrite N2Z.inj_pow. apply toZ_bounds.
      exact H1.
      eapply Z.lt_le_trans. apply toZ_bounds. apply Z.pow_le_mono_r. reflexivity. apply N2Z.inj_le, N.le_pred_l.
Qed.

Theorem toZ_nop:
  forall zop nop w n1 n2
    (N2Z: Z.of_N (nop n1 n2) = zop (Z.of_N n1) (Z.of_N n2))
    (MOD: forall z1 z2, w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  toZ w (nop n1 n2) = canonicalZ (Z.of_N w) (zop (toZ w n1) (toZ w n2)).
Proof.
  intros. destruct w as [|w]. rewrite canonicalZ_0_l. apply toZ_0_l.
  unfold toZ at 1. rewrite N2Z.
  unfold toZ. unfold canonicalZ at 3 4. symmetry.
  erewrite <- canonicalZ_mod_pow2; [| apply N2Z.is_nonneg | reflexivity ].
  rewrite MOD, !Zminus_mod_idemp_l, !Z.add_simpl_r, <- MOD by discriminate.
  apply canonicalZ_mod_pow2. apply N2Z.is_nonneg. reflexivity.
Qed.

Corollary nop_sbop2:
  forall zop nop w n1 n2
    (N2Z: Z.of_N (nop n1 n2) = zop (Z.of_N n1) (Z.of_N n2))
    (MOD: forall z1 z2, w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  (nop n1 n2) mod 2^w = sbop2 zop w n1 n2.
Proof.
  intros. apply (toZ_inj w). apply mp2_mod_lt. apply ofZ_bound.
  unfold sbop2. rewrite toZ_mod_pow2, toZ_ofZ_canonicalZ by reflexivity. apply toZ_nop; assumption.
Qed.

Corollary nop_sbop1:
  forall zop nop w n
    (N2Z: Z.of_N (nop n) = zop (Z.of_N n))
    (MOD: forall z, w <> 0 -> ((zop z) mod 2^Z.of_N w = (zop (z mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  (nop n) mod 2^w = ofZ w (zop (toZ w n)).
Proof.
  intros zop nop.
  pose (nop1 (n1:N) := nop). pose (zop1 (z1:Z) := zop).
  change nop with (nop1 N0). change zop with (zop1 Z0).
  intros. rewrite <- (toZ_0_r w). apply nop_sbop2. apply N2Z.
  intro. apply MOD.
Qed.

Theorem ofZ_zop2:
  forall zop nop w z1 z2
    (N2Z: Z.of_N (nop (ofZ w z1) (ofZ w z2)) = zop (Z.of_N (ofZ w z1)) (Z.of_N (ofZ w z2)))
    (MOD: w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  ofZ w (zop z1 z2) = (nop (ofZ w z1) (ofZ w z2)) mod 2^w.
Proof.
  intros. destruct w as [|w]. rewrite N.mod_1_r. apply ofZ_0_l.
  unfold ofZ at 1. apply N2Z.inj.
  rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  rewrite N2Z.
  rewrite !Z2N.id by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  unfold ofZ. rewrite !Z2N.id by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  rewrite N2Z.inj_pow. apply MOD. discriminate.
Qed.

Corollary ofZ_zop1:
  forall zop nop w z
    (N2Z: Z.of_N (nop (ofZ w z)) = zop (Z.of_N (ofZ w z)))
    (MOD: w <> 0 -> ((zop z) mod 2^Z.of_N w = (zop (z mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  ofZ w (zop z) = (nop (ofZ w z)) mod 2^w.
Proof.
  intros zop nop.
  pose (nop1 (n1 n2:N) := nop n2). pose (zop1 (z1 z2:Z) := zop z2).
  change nop with (nop1 N0). change zop with (zop1 Z0).
  intros. rewrite <- (ofZ_0_r w). apply ofZ_zop2; assumption.
Qed.

Theorem add_sbop:
  forall w n1 n2, (n1 + n2) mod 2^w = ofZ w (toZ w n1 + toZ w n2).
Proof.
  intros. apply nop_sbop2.
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_add:
  forall w z1 z2, ofZ w (z1 + z2) = (ofZ w z1 + ofZ w z2) mod 2^w.
Proof.
  intros. apply ofZ_zop2.
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem toZ_add:
  forall w n1 n2, toZ w (N.add n1 n2) = canonicalZ (Z.of_N w) (Z.add (toZ w n1) (toZ w n2)).
Proof.
  intros. apply (toZ_nop Z.add N.add).
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem sub_sbop:
  forall w n1 n2, n2 < 2^w -> (n1 + (2^w - n2)) mod 2^w = ofZ w (toZ w n1 - toZ w n2).
Proof.
  intros.
  rewrite N.add_sub_assoc, N.add_comm by apply N.lt_le_incl, H.
  erewrite <- mp2_mod_mod, <- ofZ_mod_pow2 by reflexivity.
  set (x := (_-_) mod _). set (y := ((_-_) mod _)%Z). pattern n1, n2 in x. pattern (toZ w n1), (toZ w n2) in y. subst x y.
  apply nop_sbop2.

    rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
    rewrite N2Z.inj_sub by (etransitivity; [ apply N.lt_le_incl, H | apply N.le_add_r ]).
    rewrite N2Z.inj_add, <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l, N2Z.inj_pow.
      reflexivity.
      rewrite N2Z.inj_pow. apply Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.

    intros. rewrite <- Zminus_mod. reflexivity.
Qed.

Theorem ofZ_sub:
  forall w z1 z2, ofZ w (z1 - z2) = (2^w + ofZ w z1 - ofZ w z2) mod 2^w.
Proof.
  intros.
  rewrite <- mp2_mod_mod, <- (ofZ_mod_pow2 w _ (_-_)) by reflexivity.
  set (x := (_ - _) mod _). set (y := (_ mod _)%Z). pattern (ofZ w z1), (ofZ w z2) in x. pattern z1, z2 in y. subst x y.
  apply ofZ_zop2.

    rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
    rewrite N2Z.inj_sub by (etransitivity; [ apply N.lt_le_incl, ofZ_bound | apply N.le_add_r ]).
    rewrite N2Z.inj_add, <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l, N2Z.inj_pow.
      reflexivity.
      rewrite N2Z.inj_pow. apply Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.

    intros. rewrite <- Zminus_mod. reflexivity.
Qed.

Theorem toZ_sub:
  forall w n1 n2 (LE: n2 <= n1),
  toZ w (n1 - n2) = canonicalZ (Z.of_N w) (toZ w n1 - toZ w n2).
Proof.
  intros. apply (toZ_nop Z.sub N.sub).
    apply N2Z.inj_sub, LE.
    intros. apply Zminus_mod.
Qed.

Theorem neg_sbop:
  forall w n, n < 2^w -> (2^w - n) mod 2^w = ofZ w (- toZ w n).
Proof.
  intros. rewrite <- (N.add_0_l (_-_)). rewrite <- Z.sub_0_l, <- (toZ_0_r w).
  apply sub_sbop. assumption.
Qed.

Theorem ofZ_neg:
  forall w z, ofZ w (-z) = (2^w - ofZ w z) mod 2^w.
Proof.
  intros. rewrite <- (N.add_0_r (2^w)) at 1. rewrite <- Z.sub_0_l, <- (ofZ_0_r w).
  apply ofZ_sub.
Qed.

Theorem mul_sbop:
  forall w n1 n2, (n1 * n2) mod 2^w = ofZ w (toZ w n1 * toZ w n2).
Proof.
  intros. apply nop_sbop2.
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_mul:
  forall w z1 z2, ofZ w (z1 * z2) = (ofZ w z1 * ofZ w z2) mod 2^w.
Proof.
  intros. apply ofZ_zop2.
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem toZ_mul:
  forall w n1 n2, toZ w (n1 * n2) = canonicalZ (Z.of_N w) (toZ w n1 * toZ w n2).
Proof.
  intros. apply (toZ_nop Z.mul N.mul).
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Remark Z_div_nonneg:
  forall a b, ((0 <= a) -> (0 <= b) -> (0 <= a / b))%Z.
Proof.
  intros a b H1 H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
    apply Z.div_pos; assumption.
    subst b. destruct a; reflexivity.
Qed.

Remark N_div_le:
  forall a b, a / b <= a.
Proof.
  intros. destruct b as [|b].
    destruct a; apply N.le_0_l.
    apply N.Div0.div_le_upper_bound.
      rewrite <- (N.mul_1_l a) at 1. apply N.mul_le_mono_r. destruct b; discriminate.
Qed.

Theorem div_sbop:
  forall w n1 n2, (n1 / n2) mod 2^w = ofZ w (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. unfold ofZ. rewrite Z2N.inj_mod.
    rewrite Z2N.inj_div, Z2N.inj_pow, !N2Z.id by first [ apply N2Z.is_nonneg | discriminate ]. reflexivity.
    apply Z_div_nonneg; apply N2Z.is_nonneg.
    apply Z.pow_nonneg. discriminate.
Qed.

Corollary div_sbop':
  forall w n1 n2, n1 < 2^w -> n1 / n2 = ofZ w (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. rewrite <- (N.mod_small (_/_) (2^w)).
    apply div_sbop.
    eapply N.le_lt_trans. apply N_div_le. apply H.
Qed.

Theorem ofZ_div:
  forall w z1 z2, ofZ w ((z1 mod 2^Z.of_N w) / (z2 mod 2^Z.of_N w)) = (ofZ w z1 / ofZ w z2) mod 2^w.
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_div by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  rewrite Z2N.inj_mod.
    rewrite Z2N.inj_pow, N2Z.id. reflexivity. discriminate. apply N2Z.is_nonneg.
    apply Z_div_nonneg; (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
    apply Z.pow_nonneg. discriminate.
Qed.

Theorem toZ_div:
  forall w n1 n2, toZ w (n1 / n2) = canonicalZ (Z.of_N w) (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. unfold toZ. rewrite N2Z.inj_div. reflexivity.
Qed.

Theorem mod_sbop:
  forall w n1 n2, n2 <> 0 -> (n1 mod n2) mod 2^w = ofZ w ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. unfold ofZ.
  rewrite !Z2N.inj_mod.
    rewrite Z2N.inj_pow.
      rewrite !N2Z.id. reflexivity.
      discriminate.
      apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
    destruct n2. contradiction. apply N2Z.is_nonneg.
    apply Z.mod_pos_bound. destruct n2. contradiction. reflexivity.
    apply Z.pow_nonneg. discriminate.
Qed.

Corollary mod_sbop':
  forall w n1 n2, 0 < n2 < 2^w -> n1 mod n2 = ofZ w ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. rewrite <- (N.mod_small (n1 mod n2) (2^w)). apply mod_sbop. apply N.neq_0_lt_0, H.
  etransitivity. apply N.mod_lt, N.neq_0_lt_0, H. apply H.
Qed.

Theorem ofZ_mod:
  forall w z1 z2, (z2 mod 2^Z.of_N w <> 0)%Z ->
  ofZ w ((z1 mod 2^Z.of_N w) mod (z2 mod 2^Z.of_N w)) = ((ofZ w z1) mod (ofZ w z2)).
Proof.
  intros.
  assert (H': (0 < 2^Z.of_N w)%Z). apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
  apply (Z.mod_pos_bound z2), proj1, Z.lt_eq_cases in H'.
  destruct H' as [H'|H']; [| rewrite <- H' in H; contradiction ].
  unfold ofZ. rewrite (Z.mod_small (_ mod _)); [|split]. apply Z2N.inj_mod.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    apply Z.lt_le_incl, H'.
    apply Z.mod_pos_bound. apply H'.
    etransitivity.
      apply Z.mod_pos_bound. apply H'.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem toZ_mod:
  forall w n1 n2, toZ w (n1 mod n2) = canonicalZ (Z.of_N w) ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z.inj_mod. reflexivity.
Qed.

Lemma Z_shiftl_eqm:
  forall w z1 z2, (0 <= z2)%Z -> eqm (2^w) (Z.shiftl z1 z2) (Z.shiftl (z1 mod 2^w) z2).
Proof.
  intros. unfold eqm. destruct (Z.neg_nonneg_cases w) as [H1|H1].
    rewrite Z.pow_neg_r, !Zmod_0_r by assumption. reflexivity.

    apply Z.bits_inj'. intros i H2.
    rewrite <- !Z.land_ones, !Z.land_spec, !Z.shiftl_spec, Z.land_spec, !Z.testbit_ones, (proj2 (Z.leb_le 0 i) H2) by assumption.
    destruct (0 <=? i - z2)%Z eqn:H3.
      destruct (i <? w)%Z eqn:H4.
        replace (i - z2 <? w)%Z with true.
          rewrite !Bool.andb_true_r. reflexivity.
          symmetry. rewrite <- (Z.sub_0_r w). apply Z.ltb_lt, Z.sub_lt_le_mono. apply Z.ltb_lt, H4. assumption.
        rewrite !Bool.andb_false_r. reflexivity.
      rewrite Z.testbit_neg_r. reflexivity. apply Z.leb_gt, H3.
Qed.

Theorem shiftl_sbop:
  forall w n1 n2, (N.shiftl n1 n2) mod 2^w = ofZ w (Z.shiftl (toZ w n1) (Z.of_N n2)).
Proof.
  intros.
  pose (nop n := N.shiftl n n2). pose (zop z := Z.shiftl z (Z.of_N n2)).
  change (N.shiftl _ _) with (nop n1). change (Z.shiftl _ _) with (zop (toZ w n1)).
  apply nop_sbop1. apply N2Z_inj_shiftl. intros. apply Z_shiftl_eqm, N2Z.is_nonneg.
Qed.

Theorem ofZ_shiftl:
  forall w z n, ofZ w (Z.shiftl z (Z.of_N n)) = (N.shiftl (ofZ w z) n) mod 2^w.
Proof.
  intros.
  pose (nop n1 := N.shiftl n1 n). pose (zop z1 := Z.shiftl z1 (Z.of_N n)).
  change (N.shiftl _ _) with (nop (ofZ w z)). change (Z.shiftl _ _) with (zop z).
  apply ofZ_zop1. apply N2Z_inj_shiftl. intro. apply Z_shiftl_eqm, N2Z.is_nonneg.
Qed.

Theorem toZ_shiftl:
  forall w n1 n2, toZ w (N.shiftl n1 n2) = canonicalZ (Z.of_N w) (Z.shiftl (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z_inj_shiftl. reflexivity. 
Qed.

Theorem shiftr_sbop:
  forall w n1 n2, (N.shiftr n1 n2) mod 2^w = ofZ w (Z.shiftr (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold ofZ.
  rewrite Z.shiftr_div_pow2 by apply N2Z.is_nonneg.
  rewrite Z2N.inj_mod.

    rewrite Z2N.inj_div; [| apply N2Z.is_nonneg | apply Z.pow_nonneg; discriminate ].
    rewrite !Z2N.inj_pow by first [ discriminate | apply N2Z.is_nonneg ].
    rewrite <- N.shiftr_div_pow2, !N2Z.id. reflexivity.

    apply Z.div_pos. apply N2Z.is_nonneg. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.

    apply Z.pow_nonneg. discriminate.
Qed.

Theorem ofZ_shiftr:
  forall w z n, ofZ w (Z.shiftr (z mod 2^Z.of_N w) (Z.of_N n)) = (N.shiftr (ofZ w z) n) mod 2^w.
Proof.
  symmetry. rewrite <- N2Z_ofZ. apply shiftr_sbop.
Qed.

Theorem toZ_shiftr:
  forall w n1 n2, toZ w (N.shiftr n1 n2) = canonicalZ (Z.of_N w) (Z.shiftr (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z_inj_shiftr. reflexivity.
Qed.

Theorem ashiftr_0_w:
  forall n1 n2, ashiftr 0 n1 n2 = 0.
Proof. intros. apply sbop1_0_l. Qed.

Theorem ashiftr_0_l:
  forall w n2, ashiftr w 0 n2 = 0.
Proof.
  intros. unfold ashiftr, sbop1. rewrite toZ_0_r, Z.shiftr_0_l. apply ofZ_0_r.
Qed.

Theorem ashiftr_0_r:
  forall w n1, ashiftr w n1 0 = n1 mod 2^w.
Proof.
  intros. unfold ashiftr, sbop1. rewrite Z.shiftr_0_r. apply ofZ_toZ.
Qed.

Theorem ashiftr_spec:
  forall w n1 n2 i, N.testbit (ashiftr w n1 n2) i = andb (i <? w) (N.testbit n1 (N.min (i + n2) (N.pred w))).
Proof.
  intros. unfold ashiftr, sbop1. destruct w as [|w].
    rewrite ofZ_0_l. destruct i; apply N.bits_0.
    rewrite testbit_ofZ, Z.shiftr_spec by apply N2Z.is_nonneg.
      rewrite <- N2Z.inj_add, testbit_toZ by discriminate. reflexivity.
Qed.

Theorem ashiftr_nonneg:
  forall w n1 n2, n1 mod 2^w < 2^N.pred w -> ashiftr w n1 n2 = N.shiftr (n1 mod 2^w) n2.
Proof.
  symmetry. unfold ashiftr, sbop1.
  rewrite (proj1 (toZ_nonneg w n1) H), <- (N.mod_small (N.shiftr _ _) (2^w)). apply shiftr_sbop.
  rewrite N.shiftr_div_pow2. eapply N.le_lt_trans. apply N_div_le. apply mp2_mod_lt.
Qed.

Theorem ashiftr_neg:
  forall w n1 n2, 2^N.pred w <= n1 mod 2^w -> ashiftr w n1 n2 = (N.shiftr (N.lor n1 (N.shiftl (N.ones n2) w)) n2) mod 2^w.
Proof.
  symmetry. destruct w as [|w].

    rewrite ashiftr_0_w. apply N.mod_1_r.

    apply N.bits_inj. intro i.
    rewrite ashiftr_spec, <- N.land_ones, N.land_spec, N.shiftr_spec', N.lor_spec, N_ones_spec_ltb, Bool.andb_comm.
    destruct (N.le_gt_cases (i+n2) (N.pred (N.pos w))).
      rewrite N.min_l by assumption. rewrite N.shiftl_spec_low, Bool.orb_false_r. reflexivity.
        eapply N.le_lt_trans. eassumption. apply N.lt_pred_l. discriminate.
      rewrite N.min_r, N.shiftl_spec_high', N_ones_spec_ltb.
        destruct (i <? N.pos w) eqn:H1; [|reflexivity]. replace (_ <? _) with true.
          rewrite Bool.orb_true_r, signbit by discriminate. symmetry. apply Z.ltb_lt. rewrite (proj1 (toZ_neg _ _) H).
            change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply Z.lt_sub_0, N2Z.inj_lt.
            apply mp2_mod_lt.
          symmetry. eapply N.ltb_lt, N.add_lt_mono_r. rewrite N.sub_add, (N.add_comm n2).
            apply N.add_lt_mono_r. apply N.ltb_lt, H1.
            apply N.lt_pred_le, H0.
        apply N.lt_pred_le, H0.
        apply N.lt_le_incl, H0.
Qed.

Definition N_ashiftr w n1 n2 :=
  (N.shiftr (N.lor (n1 mod 2^w) (if N.testbit n1 (N.pred w) then N.shiftl (N.ones n2) w else 0)) n2) mod 2^w.

Theorem ashiftr_sbop:
  forall w n1 n2, N_ashiftr w n1 n2 = ashiftr w n1 n2.
Proof.
  symmetry. unfold N_ashiftr. destruct w as [|w].
    rewrite N.mod_1_r. apply ashiftr_0_w.
    unfold ashiftr, sbop1. rewrite signbit by discriminate. destruct (_ <? 0)%Z eqn:H.
      rewrite <- toZ_mod_pow2 at 1 by reflexivity. apply ashiftr_neg. rewrite mp2_mod_mod.
        apply N.nlt_ge. intro H1. apply (proj2 (Bool.not_false_iff_true _) H), Z.ltb_ge, toZ_sign, H1.
      rewrite N.lor_0_r, N.mod_small.
        apply ashiftr_nonneg, toZ_sign, Z.ltb_ge, H.
        rewrite N.shiftr_div_pow2. eapply N.le_lt_trans. apply N_div_le. apply mp2_mod_lt.
Qed.

Corollary ofZ_ashiftr:
  forall w z n, ofZ w (Z.shiftr (canonicalZ (Z.of_N w) z) (Z.of_N n)) = N_ashiftr w (ofZ w z) n.
Proof.
  symmetry. rewrite ashiftr_sbop. erewrite <- toZ_ofZ_canonicalZ; reflexivity.
Qed.

Theorem land_sbop:
  forall w n1 n2, (N.land n1 n2) mod 2^w = ofZ w (Z.land (toZ w n1) (toZ w n2)).
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_land.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_assoc, (Z.land_comm _ z2), <- !Z.land_assoc, !Z.land_diag, !Z.land_assoc, (Z.land_comm z2 z1).
      reflexivity.
Qed.

Theorem ofZ_land:
  forall w z1 z2, ofZ w (Z.land z1 z2) = N.land (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.land _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_land.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_assoc, (Z.land_comm _ z2), <- !Z.land_assoc, !Z.land_diag, !Z.land_assoc, (Z.land_comm z2 z1).
      reflexivity.
    apply hibits_zero_bound. intros. rewrite N.land_spec, testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_land:
  forall w n1 n2, toZ w (N.land n1 n2) = Z.land (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.land _ _)).
    apply (toZ_nop Z.land N.land).
      apply N2Z_inj_land.
      intros. rewrite <- !Z.land_ones by apply N2Z.is_nonneg. rewrite (Z.land_comm z1 (Z.ones _)), <- !Z.land_assoc,
        (Z.land_comm (Z.ones _)), <- !Z.land_assoc, !Z.land_diag. reflexivity.
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.land_spec.
      repeat rewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lor_sbop:
  forall w n1 n2, (N.lor n1 n2) mod 2^w = ofZ w (Z.lor (toZ w n1) (toZ w n2)).
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_lor.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_lor_distr_l, <- !Z.land_assoc, Z.land_diag. symmetry. apply Z.land_lor_distr_l.
Qed.

Theorem ofZ_lor:
  forall w z1 z2, ofZ w (Z.lor z1 z2) = N.lor (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.lor _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_lor.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_lor_distr_l, <- !Z.land_assoc, Z.land_diag. symmetry. apply Z.land_lor_distr_l.
    apply hibits_zero_bound. intros. rewrite !N.lor_spec, !testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_lor:
  forall w n1 n2, toZ w (N.lor n1 n2) = Z.lor (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.lor _ _)).
    apply (toZ_nop Z.lor N.lor).
      apply N2Z_inj_lor.
      intros. rewrite <- !Z.land_ones, <- Z.land_lor_distr_l, <- Z.land_assoc, Z.land_diag by apply N2Z.is_nonneg.
        reflexivity.
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.lor_spec.
      repeat erewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lxor_sbop:
  forall w n1 n2, (N.lxor n1 n2) mod 2^w = ofZ w (Z.lxor (toZ w n1) (toZ w n2)).
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_lxor.
    intros. apply Z.bits_inj. intro i. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. repeat destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lxor:
  forall w z1 z2, ofZ w (Z.lxor z1 z2) = N.lxor (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.lxor _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_lxor.
    intros. apply Z.bits_inj. intro i. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. repeat destruct (Z.testbit _ _); reflexivity.
    apply hibits_zero_bound. intros. rewrite !N.lxor_spec, !testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_lxor:
  forall w n1 n2, toZ w (N.lxor n1 n2) = Z.lxor (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.lxor _ _)).
    apply (toZ_nop Z.lxor N.lxor). apply N2Z_inj_lxor.
      intros. apply Z.bits_inj'. intros i H1.
      rewrite <- !Z.land_ones, !Z.land_spec, !Z.lxor_spec, !Z.land_spec by apply N2Z.is_nonneg.
      destruct (Z.lt_ge_cases i (Z.of_N w)) as [H2|H2].
        rewrite Z.ones_spec_low.
          rewrite !Bool.andb_true_r. reflexivity.
          split. exact H1. exact H2.
        rewrite Z.ones_spec_high.
          rewrite !Bool.andb_false_r. reflexivity.
          split. apply N2Z.is_nonneg. exact H2.  
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.lxor_spec.
      repeat erewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lnot_sbop:
  forall w n, (N.lnot n w) mod 2^w = ofZ w (Z.lnot (toZ w n)).
Proof.
  intros. destruct w as [|w].
    rewrite ofZ_0_l. apply N.mod_1_r.
    apply N.bits_inj. intro i. unfold N.lnot.
      rewrite <- N.land_ones, N.land_spec, N.lxor_spec, testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
      rewrite testbit_toZ, N_ones_spec_ltb, Bool.andb_comm by discriminate.
      destruct (i <? N.pos w) eqn:H.
        rewrite N.min_l by apply N.lt_le_pred, N.ltb_lt, H. reflexivity.
        reflexivity.
Qed.

Theorem ofZ_lnot:
  forall w z, ofZ w (Z.lnot z) = N.lnot (ofZ w z) w.
Proof.
  intros. apply N.bits_inj. intro b. destruct (N.lt_ge_cases b w).

    rewrite N.lnot_spec_low by assumption.
    rewrite !testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
    apply N.ltb_lt in H. rewrite H. reflexivity.

    rewrite N.lnot_spec_high by assumption.
    rewrite !testbit_ofZ. apply N.ltb_ge in H. rewrite H. reflexivity.
Qed.

Theorem toZ_lnot:
  forall w n, w <> 0 -> toZ w (N.lnot n w) = Z.lnot (toZ w n).
Proof.
  intros. apply Z.bits_inj'. intros b H1. rewrite <- (Z2N.id _ H1).
  destruct (N.lt_ge_cases (Z.to_N b) w) as [H2|H2].
    rewrite Z.lnot_spec by apply N2Z.is_nonneg. rewrite !testbit_toZ by exact H. rewrite N.min_l.
      rewrite N.lnot_spec_low by assumption. reflexivity.
      apply N.lt_le_pred. assumption.
    rewrite Z.lnot_spec by apply N2Z.is_nonneg. rewrite !testbit_toZ by exact H. rewrite N.min_r.
      rewrite N.lnot_spec_low. reflexivity. apply N.lt_pred_l, H.
      transitivity w. apply N.le_pred_l. apply H2.
Qed.

Theorem eqb_sbop:
  forall w n1 n2, N.eqb (n1 mod 2^w) (n2 mod 2^w) = Z.eqb (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (toZ_mod_pow2 w _ n1), <- (toZ_mod_pow2 w _ n2) by reflexivity.
  destruct (N.eq_dec (n1 mod 2^w) (n2 mod 2^w)).
    rewrite e. rewrite Z.eqb_refl. apply N.eqb_refl.
    rewrite (proj2 (N.eqb_neq _ _) n). symmetry. apply Z.eqb_neq. intro H. apply n, (toZ_inj w).
      apply mp2_mod_lt.
      apply mp2_mod_lt.
      exact H.
Qed.

Theorem eqb_ofZ:
  forall w z1 z2, N.eqb (ofZ w z1) (ofZ w z2) = (Z.eqb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (Z.eq_dec (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)).
    rewrite e. rewrite Z.eqb_refl. apply N.eqb_refl.
    rewrite (proj2 (Z.eqb_neq _ _) n). apply N.eqb_neq. intro H. apply n, Z2N.inj.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
      exact H.
Qed.

Theorem ltb_sbop:
  forall w n1 n2, N.ltb ((n1 + 2^N.pred w) mod 2^w) ((n2 + 2^N.pred w) mod 2^w) = Z.ltb (toZ w n1) (toZ w n2).
Proof.
  intros. destruct w as [|w]. rewrite !toZ_0_l, !N.mod_1_r. reflexivity.
  unfold toZ, canonicalZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pred, <- !N2Z.inj_pow, <- !N2Z.inj_add by reflexivity.
  rewrite <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  assert (H: forall x y z, ((x-y <? z-y) = (x <? z))%Z). intros. destruct (x <? z)%Z eqn:H.
    apply Z.ltb_lt, Z.sub_lt_mono_r, Z.ltb_lt, H.
    apply Z.ltb_ge, Z.sub_le_mono_r, Z.ltb_ge, H.
  rewrite !H, N2Z_inj_ltb. reflexivity.
Qed.

Theorem ltb_ofZ:
  forall w z1 z2, N.ltb (ofZ w z1) (ofZ w z2) = (Z.ltb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (_ <? _)%Z eqn:H.
    apply N.ltb_lt, Z2N.inj_lt; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.ltb_lt, H.
    apply N.ltb_ge, Z2N.inj_le; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.ltb_ge, H.
Qed.

Theorem leb_sbop:
  forall w n1 n2, N.leb ((n1 + 2^N.pred w) mod 2^w) ((n2 + 2^N.pred w) mod 2^w) = Z.leb (toZ w n1) (toZ w n2).
Proof.
  intros. destruct w as [|w]. rewrite !toZ_0_l, !N.mod_1_r. reflexivity.
  unfold toZ, canonicalZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pred, <- !N2Z.inj_pow, <- !N2Z.inj_add by reflexivity.
  rewrite <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  assert (H: forall x y z, ((x-y <=? z-y) = (x <=? z))%Z). intros. destruct (x <=? z)%Z eqn:H.
    apply Z.leb_le, Z.sub_le_mono_r, Z.leb_le, H.
    apply Z.leb_gt, Z.sub_lt_mono_r, Z.leb_gt, H.
  rewrite !H, N2Z_inj_leb. reflexivity.
Qed.

Theorem leb_ofZ:
  forall w z1 z2, N.leb (ofZ w z1) (ofZ w z2) = (Z.leb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (_ <=? _)%Z eqn:H.
    apply N.leb_le, Z2N.inj_le; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.leb_le, H.
    apply N.leb_gt, Z2N.inj_lt; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.leb_gt, H.
Qed.

Theorem xbits_ofZ:
  forall w z i j, xbits (ofZ w z) i j = Z.to_N (Z_xbits z (Z.of_N i) (Z.of_N (N.min j w))).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite <- (N2Z.id b) at 2. rewrite <- Z2N.inj_testbit by apply N2Z.is_nonneg. rewrite Z2N.id.
    rewrite xbits_spec, testbit_ofZ, Z_xbits_spec, <- N2Z.inj_add, N2Z_inj_ltb, Zle_imp_le_bool,
            Bool.andb_true_r, Bool.andb_comm, Bool.andb_assoc, Bool.andb_comm by apply N2Z.is_nonneg.
            apply f_equal. destruct (_ <? N.min _ _) eqn:H.
      apply N.ltb_lt, N.min_glb_lt_iff in H. destruct H. rewrite !(proj2 (N.ltb_lt _ _)) by assumption. reflexivity.
      apply N.ltb_ge, N.min_le in H. destruct H as [H|H]; apply N.ltb_ge in H; rewrite H.
        reflexivity.
        apply Bool.andb_false_r.
    apply Z_xbits_nonneg.
Qed.

Theorem msub_lt:
  forall w x y, msub w x y < 2^w.
Proof. intros. apply mp2_mod_lt. Qed.

Theorem msub_0:
  forall x y, msub 0 x y = 0.
Proof.
  intros. apply N.mod_1_r.
Qed.

Theorem msub_mod_l:
  forall w w' x y, w <= w' -> msub w (x mod 2^w') y = msub w x y.
Proof.
  intros. unfold msub.
  rewrite <- mp2_add_l, mp2_mod_mod_min, N.min_r, mp2_add_l by assumption.
  reflexivity.
Qed.

Theorem msub_mod_r:
  forall w w' x y, w <= w' -> msub w x (y mod 2^w') = msub w x y.
Proof.
  intros. unfold msub.
  rewrite mp2_mod_mod_min, N.min_r by assumption.
  reflexivity.
Qed.

Theorem msub_sbop:
  forall w x y, msub w x y = ofZ w (toZ w x - toZ w y).
Proof.
  intros.
  rewrite <- (toZ_mod_pow2 w w y) by reflexivity.
  unfold msub.
  apply sub_sbop, mp2_mod_lt.
Qed.

Theorem toZ_msub:
  forall w x y, toZ w (msub w x y) = canonicalZ (Z.of_N w) (toZ w x - toZ w y).
Proof.
  intros. rewrite msub_sbop. apply toZ_ofZ_canonicalZ. reflexivity.
Qed.

Theorem N2Z_msub:
  forall w m n, Z.of_N (msub w m n) = ((Z.of_N m - Z.of_N n) mod 2^Z.of_N w)%Z.
Proof.
  intros. unfold msub.
  rewrite N2Z.inj_mod, N2Z.inj_add, N2Z.inj_sub by apply N.lt_le_incl, mp2_mod_lt.
  rewrite N2Z.inj_mod.
  rewrite Z.add_sub_assoc, Zminus_mod_idemp_r, Z.add_comm, <- Z.add_sub_assoc.
  rewrite <- Z.add_mod_idemp_l, Z.mod_same by apply N2Z_pow2_nonzero.
  rewrite N2Z.inj_pow. reflexivity.
Qed.

Theorem msub_diag:
  forall w x, msub w x x = 0.
Proof.
  intros. rewrite msub_sbop, Z.sub_diag. reflexivity.
Qed.

Theorem msub_0_r:
  forall w x, msub w x 0 = x mod 2^w.
Proof.
  intros. rewrite msub_sbop, toZ_0_r, Z.sub_0_r. apply ofZ_toZ.
Qed.

Theorem msub_0_l:
  forall w x, msub w 0 x = (2^w - x mod 2^w) mod 2^w.
Proof. reflexivity. Qed.

Theorem msub_0_l_neg:
  forall w x, msub w 0 x = ofZ w (- toZ w x).
Proof.
  intros. rewrite msub_sbop, toZ_0_r, Z.sub_0_l. reflexivity.
Qed.

Theorem msub_mod_pow2:
  forall w w' x y, (msub w x y) mod 2^w' = msub (N.min w w') x y.
Proof.
  intros. unfold msub at 1. rewrite mp2_mod_mod_min.
  destruct (N.le_ge_cases w w').
    rewrite N.min_l by assumption. reflexivity.

    rewrite <- mp2_add_r, N_sub_mod;
    [| apply N.pow_nonzero; discriminate 1 | apply N.lt_le_incl, mp2_mod_lt ].
    rewrite mp2_mod_mod_min, !N.min_r by assumption.
    rewrite <- (N.sub_add _ _ H) at 1 2.
    rewrite N.pow_add_r, N.Div0.mod_mul.
    destruct (y mod 2^w') eqn:H1 at 1.
      erewrite N.mul_0_r, <- msub_mod_r, H1, N.add_0_r, msub_0_r by reflexivity. reflexivity.
      rewrite N.mul_1_r. reflexivity.
Qed.

Theorem msub_add:
  forall w x y, (msub w x y + y) mod 2^w = x mod 2^w.
Proof.
  intros.
  rewrite msub_sbop, <- mp2_add_r, <- (ofZ_toZ w y), <- ofZ_add, Z.sub_add.
  apply ofZ_toZ.
Qed.

Corollary add_msub:
  forall w x y, (x + msub w y x) mod 2^w = y mod 2^w.
Proof.
  intros. rewrite N.add_comm. apply msub_add.
Qed.

Theorem add_msub_r:
  forall w x y, msub w (x+y) y = x mod 2^w.
Proof.
  intros. rewrite msub_sbop, toZ_add, canonicalZ_sub_l, Z.add_simpl_r. apply ofZ_toZ.
Qed.

Corollary add_msub_l:
  forall w x y, msub w (x+y) x = y mod 2^w.
Proof.
  intros. rewrite N.add_comm. apply add_msub_r.
Qed.

Theorem msub_comm:
  forall w x y z, msub w (msub w x y) z = msub w (msub w x z) y.
Proof.
  intros. rewrite !msub_sbop.
  erewrite !toZ_ofZ_canonicalZ by reflexivity.
  rewrite !canonicalZ_sub_l, <- !Z.sub_add_distr, Z.add_comm.
  reflexivity.
Qed.

Theorem msub_msub_distr:
  forall w x y z, msub w x (msub w y z) = ((msub w x y) + z) mod 2^w.
Proof.
  intros. rewrite !msub_sbop, add_sbop. unfold sbop2.
  erewrite !toZ_ofZ_canonicalZ by reflexivity.
  rewrite canonicalZ_sub_r, canonicalZ_add_l, Z.sub_sub_distr.
  reflexivity.
Qed.

Theorem msub_add_distr:
  forall w x y z, msub w x (y+z) = msub w (msub w x y) z.
Proof.
  intros. rewrite !msub_sbop, toZ_add.
  erewrite toZ_ofZ_canonicalZ by reflexivity.
  rewrite canonicalZ_sub_r, canonicalZ_sub_l, Z.sub_add_distr. reflexivity.
Qed.

Theorem add_msub_assoc:
  forall w m n p, (m + msub w n p) mod 2^w = msub w (m + n) p.
Proof.
  intros.
  rewrite !msub_sbop, toZ_add, canonicalZ_sub_l, <- Z.add_sub_assoc, ofZ_add, ofZ_toZ, mp2_add_l.
  reflexivity.
Qed.

Theorem add_msub_swap:
  forall w m n p, msub w (m + n) p = (msub w m p + n) mod 2^w.
Proof.
  intros.
  rewrite !msub_sbop, toZ_add, canonicalZ_sub_l, Z.add_sub_swap, ofZ_add, ofZ_toZ, mp2_add_r.
  reflexivity.
Qed.

Theorem msub_cancel_l:
  forall w m n p, msub w m n = msub w m p <-> n mod 2^w = p mod 2^w.
Proof.
  split; intro; [|unfold msub; rewrite H; reflexivity].
  rewrite !msub_sbop in H.
  apply f_equal with (f := fun x => (2^w + ((x + ofZ w (toZ w n)) mod 2^w + ofZ w (toZ w p)) mod 2^w
                                     - ofZ w (toZ w m)) mod 2^w) in H.
  symmetry in H.
  rewrite <- !ofZ_add, <- Z.add_assoc, (Z.add_comm (toZ w n)), Z.add_assoc, !Z.sub_add,
          <- !ofZ_sub, !Z.add_simpl_l, !ofZ_toZ in H.
  assumption.
Qed.

Theorem msub_cancel_r:
  forall w m n p, msub w m p = msub w n p <-> m mod 2^w = n mod 2^w.
Proof.
  split; intro.

    rewrite !msub_sbop in H.
    apply f_equal with (f := fun x => (x + ofZ w (toZ w p)) mod 2^w) in H.
    rewrite <- !ofZ_add, !Z.sub_add, !ofZ_toZ in H.
    assumption.

    erewrite <- msub_mod_l by reflexivity. rewrite H. apply msub_mod_l. reflexivity.
Qed.

Theorem msub_move_0_r:
  forall w m n, msub w m n = 0 <-> m mod 2^w = n mod 2^w.
Proof.
  split; intro.
    eapply msub_cancel_r. rewrite (msub_diag w n). assumption.
    erewrite <- msub_mod_l, H, msub_mod_l by reflexivity. apply msub_diag.
Qed.

Theorem madd_add_simpl_r_r:
  forall w m n p, msub w (m+n) (p+n) = msub w m p.
Proof.
  intros.
  rewrite !msub_sbop, !toZ_add, canonicalZ_sub, Z.add_add_simpl_r_r.
  reflexivity.
Qed.

Theorem madd_add_simpl_r_l:
  forall w m n p, msub w (m+n) (n+p) = msub w m p.
Proof.
  intros.
  rewrite !msub_sbop, !toZ_add, canonicalZ_sub, Z.add_add_simpl_r_l.
  reflexivity.
Qed.

Theorem madd_add_simpl_l_r:
  forall w m n p, msub w (m+n) (p+m) = msub w n p.
Proof.
  intros.
  rewrite !msub_sbop, !toZ_add, canonicalZ_sub, Z.add_add_simpl_l_r.
  reflexivity.
Qed.

Theorem madd_add_simpl_l_l:
  forall w m n p, msub w (m+n) (m+p) = msub w n p.
Proof.
  intros.
  rewrite !msub_sbop, !toZ_add, canonicalZ_sub, Z.add_add_simpl_l_l.
  reflexivity.
Qed.

Theorem msub_add_simpl_r_r:
  forall w m n p, (msub w m n + (p + n)) mod 2^w = (m + p) mod 2^w.
Proof.
  intros.
  rewrite (N.add_comm p n), N.add_assoc, <- mp2_add_l, msub_add, mp2_add_l.
  reflexivity.
Qed.

Corollary msub_add_simpl_r_l:
  forall w m n p, (msub w m n + (n+p)) mod 2^w = (m+p) mod 2^w.
Proof.
  intros. rewrite (N.add_comm n p). apply msub_add_simpl_r_r.
Qed.

Theorem msub_tele:
  forall w x y z, msub w y x <= msub w z x -> msub w y x + msub w z y = msub w z x.
Proof.
  intros.
  rewrite <- (N.sub_add _ _ H), N.add_comm. apply N.add_cancel_r.
  apply (toZ_inj w).
    apply msub_lt.
    eapply N.le_lt_trans. apply N.le_sub_l. apply msub_lt.
  rewrite toZ_sub by assumption.
  rewrite !toZ_msub.
  rewrite <- (toZ_ofZ_canonicalZ w w (canonicalZ _ _ - canonicalZ _ _)) by reflexivity.
  rewrite canonicalZ_sub.
  rewrite Z.sub_sub_distr, <- Z.add_sub_swap, Z.sub_add.
  symmetry. apply toZ_ofZ_canonicalZ. reflexivity.
Qed.

Theorem msub_mtele:
  forall w x y z, (msub w y x + msub w z y) mod 2^w = msub w z x.
Proof.
  intros. rewrite !msub_sbop, <- ofZ_add.
  rewrite Z.add_comm, <- Z.sub_sub_distr, (Z.sub_sub_distr (toZ w y)), Z.sub_diag.
  reflexivity.
Qed.

Theorem mul_msub_distr_l:
  forall w m n p, (m * msub w n p) mod 2^w = msub w (m*n) (m*p).
Proof.
  intros. rewrite !msub_sbop.
  rewrite <- mp2_mul_l.
  rewrite <- (ofZ_toZ w m) at 1.
  rewrite <- ofZ_mul, !toZ_mul, canonicalZ_sub, Z.mul_sub_distr_l.
  reflexivity.
Qed.

Corollary mul_msub_distr_r:
  forall w m n p, (msub w m n * p) mod 2^w = msub w (m*p) (n*p).
Proof.
  intros. rewrite !(N.mul_comm _ p). apply mul_msub_distr_l.
Qed.

Theorem msub_sub:
  forall w x y, y <= x -> msub w x y = (x - y) mod 2^w.
Proof.
  intros. unfold msub.
  rewrite N.add_sub_assoc by apply N.lt_le_incl, mp2_mod_lt.
  rewrite N.add_comm, <- N.add_sub_assoc by (etransitivity; [ apply mp2_mod_le | apply H ]).
  rewrite <- mp2_add_l, mp2_mod_same, N.add_0_l.
  erewrite <- (N.add_sub x) at 1. rewrite <- N.sub_add_distr, <- mp2_div_mod.
  rewrite N.add_comm, <- N.add_sub_assoc by assumption.
  rewrite N.add_comm, N.mul_comm, mp2_mod_add. reflexivity.
Qed.

Theorem msub_nowrap:
  forall w x y, x mod 2^w <= y mod 2^w -> msub w y x = y mod 2^w - x mod 2^w.
Proof.
  intros. rewrite msub_sbop, ofZ_sub, !ofZ_toZ, <- N.add_sub_assoc by assumption.
  rewrite <- mp2_add_l, mp2_mod_same.
  eapply N.mod_small, N.le_lt_trans.
    apply N.le_sub_l.
    apply mp2_mod_lt.
Qed.

Theorem msub_wrap:
  forall w x y, x mod 2^w < y mod 2^w -> msub w x y = 2^w + x mod 2^w - y mod 2^w.
Proof.
  intros. rewrite msub_sbop. rewrite ofZ_sub. rewrite !ofZ_toZ. apply N.mod_small.
  eapply N.add_lt_mono_r. rewrite N.sub_add.
    apply N.add_lt_mono_l. assumption.
    eapply N.lt_le_incl, N.lt_le_trans.
      apply mp2_mod_lt.
      apply N.le_add_r.
Qed.

Theorem msub_inv:
  forall w x y, x mod 2^w <> y mod 2^w -> msub w x y + msub w y x = 2^w.
Proof.
  intro w. eenough (H: _).
  intros. apply N.lt_gt_cases in H0. destruct H0.
    revert x y H0. exact H.
    rewrite N.add_comm. revert y x H0. exact H.
  intros. rewrite (msub_wrap _ _ _ H0). rewrite msub_nowrap.
    rewrite N.add_sub_assoc.
      rewrite N.sub_add.
        apply N.add_sub.
        etransitivity.
          apply N.lt_le_incl, mp2_mod_lt.
          apply N.le_add_r.
      apply N.lt_le_incl. assumption.
    apply N.lt_le_incl. assumption.
Qed.

Theorem msub_inv_mod:
  forall w x y, (msub w x y + msub w y x) mod 2^w = 0.
Proof.
  intros. destruct (N.eq_dec (x mod 2^w) (y mod 2^w)).
    erewrite <- msub_mod_l, <- (msub_mod_r w w y), e, msub_mod_l, msub_mod_r, msub_diag
             by reflexivity. apply mp2_mod_0_l.
    rewrite msub_inv by assumption. apply mp2_mod_same.
Qed.

Theorem msub_neg:
  forall w x y, msub w x y = (2^w - msub w y x) mod 2^w.
Proof.
  intros.
  erewrite <- (N.add_0_l (_-_)), <- msub_inv_mod, mp2_add_l.
  rewrite N.add_sub_assoc by apply N.lt_le_incl, msub_lt.
  rewrite N.add_comm, N.add_assoc, N.add_sub, <- mp2_add_l, mp2_mod_same.
  symmetry. apply N.mod_small, msub_lt.
Qed.

Theorem msub_lt_mono_r:
  forall w m n p,
    (p mod 2^w <= N.min (m mod 2^w) (n mod 2^w) \/
     N.max (m mod 2^w) (n mod 2^w) < p mod 2^w) ->
  ((m mod 2^w < n mod 2^w) <-> (msub w m p < msub w n p)).
Proof.
  intros.
  destruct H; [ apply N.min_glb_iff in H | apply N.max_lub_lt_iff in H ];
      destruct H as [H1 H2].
    rewrite !msub_nowrap by assumption. split; intro.
      eapply N.add_lt_mono_r. rewrite !N.sub_add; assumption.
      eapply N.add_lt_mono_r in H. rewrite !N.sub_add in H; assumption.
    rewrite !msub_wrap by assumption. split; intro.
      apply N.lt_add_lt_sub_r. rewrite N.sub_add.
        apply N.add_lt_mono_l. assumption.
        etransitivity.
          apply N.lt_le_incl, mp2_mod_lt.
          apply N.le_add_r.
      apply N.lt_add_lt_sub_r in H. rewrite N.sub_add in H.
        apply N.add_lt_mono_l in H. assumption.
        etransitivity.
          apply N.lt_le_incl, mp2_mod_lt.
          apply N.le_add_r.
Qed.

Theorem msub_le_mono_r:
  forall w m n p,
    (p mod 2^w <= N.min (m mod 2^w) (n mod 2^w) \/
     N.max (m mod 2^w) (n mod 2^w) < p mod 2^w) ->
  ((m mod 2^w <= n mod 2^w) <-> (msub w m p <= msub w n p)).
Proof.
  intros. apply msub_lt_mono_r in H. destruct H as [H1 H2].
  split; intro H; apply N.le_lteq in H; destruct H.
    apply N.lt_le_incl, H1, H.
    erewrite <- msub_mod_l, H, msub_mod_l; reflexivity.
    apply N.lt_le_incl, H2, H.
    erewrite <- msub_add, H, msub_add. reflexivity.
Qed.

Theorem msub_lt_imono_r:
  forall w m n p,
    m mod 2^w < p mod 2^w ->
    p mod 2^w <= n mod 2^w ->
  msub w n p < msub w m p.
Proof.
  intros.
  rewrite msub_nowrap, msub_wrap by assumption.
  apply N.lt_add_lt_sub_r. rewrite N.sub_add by assumption.
  eapply N.lt_le_trans.
    apply mp2_mod_lt.
    apply N.le_add_r.
Qed.

Theorem msub_lt_mono_l:
  forall w m n p,
    m mod 2^w <= p mod 2^w ->
    p mod 2^w < n mod 2^w ->
  msub w p m < msub w p n.
Proof.
  intros.
  rewrite msub_nowrap, msub_wrap by assumption.
  apply N.lt_add_lt_sub_r.
  rewrite <- N.add_sub_swap by assumption.
  rewrite (N.add_comm (2^w)).
  rewrite <- N.add_sub_assoc.
    apply N.add_lt_mono_l. eapply N.le_lt_trans.
      apply N.le_sub_l.
      apply mp2_mod_lt.
    etransitivity. eassumption. apply N.lt_le_incl. assumption.
Qed.

Theorem msub_lt_imono_l:
  forall w m n p,
    (p mod 2^w < N.min (m mod 2^w) (n mod 2^w) \/
     N.max (m mod 2^w) (n mod 2^w) <= p mod 2^w) ->
  ((m mod 2^w < n mod 2^w) <-> (msub w p n < msub w p m)).
Proof.
  intros. destruct H; [ apply N.min_glb_lt_iff in H | apply N.max_lub_iff in H ];
      destruct H as [H1 H2].
    rewrite !msub_wrap by assumption. split; intro; (eapply N.le_lt_add_lt;
    [ apply N.le_succ_l, H
    | rewrite N.add_succ_r, ?(N.add_comm (_ mod _)), !N.sub_add by (etransitivity;
        [ apply N.lt_le_incl, mp2_mod_lt | apply N.le_add_r ]);
      apply N.lt_succ_diag_r ]).
    rewrite !msub_nowrap by assumption. split; intro; (eapply N.le_lt_add_lt;
      [ apply N.le_succ_l, H
      | rewrite N.add_succ_r, ?(N.add_comm (_ mod _)), !N.sub_add by assumption;
        apply N.lt_succ_diag_r ]).
Qed.

Theorem msub_le_imono_l:
  forall w m n p,
    (p mod 2^w < N.min (m mod 2^w) (n mod 2^w) \/
     N.max (m mod 2^w) (n mod 2^w) <= p mod 2^w) ->
  ((m mod 2^w <= n mod 2^w) <-> (msub w p n <= msub w p m)).
Proof.
  intros. apply msub_lt_imono_l in H. destruct H as [H1 H2].
  split; intro H; apply N.le_lteq in H; destruct H.
    apply N.lt_le_incl, H1, H.
    erewrite <- msub_mod_r, <- H, msub_mod_r; reflexivity.
    apply N.lt_le_incl, H2, H.
    apply msub_cancel_l in H. rewrite H. reflexivity.
Qed.

Theorem le_msub_l:
  forall w m n,
  n mod 2^w <= m mod 2^w <-> msub w m n <= m mod 2^w.
Proof.
  split; intro.
    rewrite (msub_nowrap _ _ _ H). apply N.le_sub_l.

    intro H1. apply H. apply N.compare_gt_iff in H1. apply N.compare_gt_iff.
    rewrite (msub_wrap _ _ _ H1), N.add_comm.
    rewrite <- N.add_sub_assoc by apply N.lt_le_incl, mp2_mod_lt.
    rewrite <- (N.add_0_r (m mod _)) at 1.
    apply N.add_lt_mono_l, N.lt_add_lt_sub_r, mp2_mod_lt.
Qed.

Corollary lt_msub_r:
  forall w m n,
  m mod 2^w < n mod 2^w <-> m mod 2^w < msub w m n.
Proof.
  split; intro; apply N.nle_gt; intro H1; contradict H.
    apply N.le_ngt, le_msub_l, H1.
    apply N.le_ngt. apply -> le_msub_l. apply H1.
Qed.

Theorem lt_msub_l:
  forall w m n,
  0 < n mod 2^w <= m mod 2^w <-> msub w m n < m mod 2^w.
Proof.
  split; intro.
    rewrite msub_nowrap; [apply N.sub_lt|]; apply H.
    split.
      erewrite <- msub_mod_r in H by reflexivity. destruct (n mod 2^w).
        contradict H. rewrite msub_0_r. apply N.lt_irrefl.
        reflexivity.

      apply N.le_ngt. intro H1. contradict H. apply N.nlt_ge.
      rewrite msub_wrap by assumption.
      rewrite N.add_comm, <- N.add_sub_assoc by apply N.lt_le_incl, mp2_mod_lt.
      rewrite <- (N.add_0_r (m mod _)) at 1.
      apply N.add_le_mono_l, N.le_add_le_sub_r, N.lt_le_incl, mp2_mod_lt.
Qed.

Corollary le_msub_r:
  forall w m n, 0 < n mod 2^w ->
  m mod 2^w < n mod 2^w <-> m mod 2^w <= msub w m n.
Proof.
  split; intro.
    apply N.le_ngt. intro H1. apply lt_msub_l in H1. contradict H0. apply N.le_ngt, H1.
    apply N.lt_nge. intro H1. contradict H0. eapply N.lt_nge, lt_msub_l. split; assumption.
Qed.

Lemma lt_msub_iff:
  forall w n m p,
    (n mod 2^w + p < m mod 2^w \/ (m mod 2^w < n mod 2^w /\ n mod 2^w + p < 2^w + m mod 2^w))
    <-> p < msub w m n.
Proof.
  split; intro.
    destruct H as [H|[H1 H2]].

      eapply N.add_lt_mono_l. eapply N.lt_le_trans. exact H.
      destruct (N.lt_ge_cases (n mod 2^w + msub w m n) (2^w)) as [H1|H1].
        rewrite <- (N.mod_small _ _ H1), N.Div0.add_mod_idemp_l, add_msub. reflexivity.
        etransitivity. apply N.lt_le_incl, mp2_mod_lt. assumption.

      rewrite msub_wrap by exact H1. apply N.lt_add_lt_sub_l, H2.

    destruct (N.lt_ge_cases (m mod 2^w) (n mod 2^w)) as [H1|H1].
      right. split.
        exact H1.
        apply N.lt_add_lt_sub_l. rewrite <- msub_wrap by exact H1. exact H.
      left. apply N.lt_add_lt_sub_l. rewrite <- msub_nowrap by exact H1. exact H.
Qed.

Lemma le_msub_iff:
  forall w n m p,
    (n mod 2^w + p <= m mod 2^w \/ (m mod 2^w < n mod 2^w /\ n mod 2^w + p <= 2^w + m mod 2^w))
    <-> p <= msub w m n.
Proof.
  split; intro.
    destruct H as [H|[H1 H2]].
      apply N.le_lteq in H. destruct H as [H|H].
        apply N.lt_le_incl, lt_msub_iff. left. exact H.
        rewrite msub_nowrap.
          rewrite <- H, N.add_comm, N.add_sub. reflexivity.
          etransitivity. apply N.le_add_r. rewrite H. reflexivity.
      apply N.le_lteq in H2. destruct H2 as [H2|H2].
        apply N.lt_le_incl, lt_msub_iff. right. split; assumption.
        rewrite msub_wrap, <- H2 by exact H1. apply N.le_add_le_sub_l. reflexivity.
    apply N.le_lteq in H. destruct H as [H|H].
      apply lt_msub_iff in H. destruct H as [H|H].
        left. apply N.lt_le_incl, H.
        right. split. apply H. apply N.lt_le_incl, H.
      subst. destruct (N.le_gt_cases (n mod 2^w) (m mod 2^w)) as [H|H].
        left. rewrite N.add_comm, msub_nowrap, N.sub_add by apply H. reflexivity.
        right. split.
          apply H.
          rewrite N.add_comm, msub_wrap, N.sub_add. reflexivity.
            etransitivity. apply N.lt_le_incl, mp2_mod_lt. apply N.le_add_r.
            apply H.
Qed.

Lemma msub_lt_iff:
  forall w n m p,
    (m mod 2^w < n mod 2^w + p /\ (n mod 2^w <= m mod 2^w \/ 2^w + m mod 2^w < n mod 2^w + p))
    <-> msub w m n < p.
Proof.
  split; intro.
    destruct H as [H1 H2]. apply N.nle_gt. intro H. apply le_msub_iff in H. destruct H as [H|H].
      revert H1. apply N.nlt_ge, H.
      destruct H as [H H']. destruct H2 as [H2|H2].
        revert H. apply N.nlt_ge, H2.
        revert H'. apply N.nle_gt, H2.
    split.
      apply N.nle_gt. intro H'. revert H. apply N.nlt_ge. apply le_msub_iff. left. exact H'. 
      edestruct N.le_gt_cases.
        left. eassumption.
        right. apply N.nle_gt. intro H'. revert H. apply N.nlt_ge, le_msub_iff.
          right. split; assumption.
Qed.

Lemma msub_le_iff:
  forall w n m p,
    (m mod 2^w <= n mod 2^w + p /\ (n mod 2^w <= m mod 2^w \/ 2^w + m mod 2^w <= n mod 2^w + p))
    <-> msub w m n <= p.
Proof.
  split; intro.
    destruct H as [H1 H2]. apply N.nlt_ge. intro H. apply lt_msub_iff in H. destruct H as [H|H].
      revert H1. apply N.nle_gt, H.
      destruct H as [H H']. destruct H2 as [H2|H2].
        revert H. apply N.nlt_ge, H2.
        revert H'. apply N.nlt_ge, H2.
    split.
      apply N.nlt_ge. intro H'. revert H. apply N.nle_gt. apply lt_msub_iff. left. exact H'.
      edestruct N.le_gt_cases.
        left. eassumption.
        right. apply N.nlt_ge. intro H'. revert H. apply N.nle_gt, lt_msub_iff.
          right. split; assumption.
Qed.

End TwosComplement.



Section OpBounds.

(* Establish upper bounds on various arithmetic and logical operations. *)

Lemma Zlt_0_pow2: forall p, (0 < Z.of_N (2^p))%Z.
Proof. intro. rewrite <- N2Z.inj_0. apply N2Z.inj_lt. apply mp2_gt_0. Qed.

Lemma N_le_div:
  forall a b c, a <= b -> a/c <= b/c.
Proof.
  intros.
  destruct c. destruct a; destruct b; reflexivity.
  intro H2. apply H, N.lt_gt. eapply N.lt_le_trans.
  rewrite (N.div_mod' b (N.pos p)) at 1.
  apply N.add_lt_mono_l. eapply (N.lt_lt_add_r _ _ (a mod N.pos p)). apply N.mod_lt. discriminate 1.
  rewrite N.add_assoc, <- N.mul_succ_r. rewrite (N.div_mod' a (N.pos p)) at 2.
  apply N.add_le_mono_r, N.mul_le_mono_l, N.le_succ_l, N.gt_lt, H2.
Qed.

Lemma div_bound: forall n1 n2, N.div n1 n2 <= n1.
Proof.
  intros.
  destruct n2. destruct n1. reflexivity. apply N.le_0_l.
  apply N.Div0.div_le_upper_bound.
  destruct n1. reflexivity.
  unfold N.le. simpl. change p0 with (1*p0)%positive at 1. rewrite Pos.mul_compare_mono_r.
  destruct p; discriminate 1.
Qed.

Lemma rem_bound:
  forall w x y (RX: signed_range w x) (RY: signed_range w y),
  signed_range w (Z.rem x y).
Proof.
  assert (BP: forall p1 p2, (0 <= Z.rem (Z.pos p1) (Z.pos p2) < Z.pos p2)%Z).
    intros. apply Z.rem_bound_pos. apply Pos2Z.is_nonneg. apply Pos2Z.is_pos.
  intros. destruct w as [|w]. apply signed_range_0_l in RX. apply signed_range_0_l in RY. subst. apply signed_range_0_r.
  destruct y as [|p2|p2]; destruct x as [|p1|p1]; try assumption;
  specialize (BP p1 p2); destruct BP as [BP1 BP2].

  (* x>0, y>0 *)
  split.
    transitivity Z0. apply Z.opp_nonpos_nonneg. apply Z.pow_nonneg. discriminate. assumption.
    transitivity (Z.pos p2). assumption. apply RY.

  (* x<0, y>0 *)
  rewrite <- Pos2Z.opp_pos, Z.rem_opp_l; [|discriminate]. split.
    apply -> Z.opp_le_mono. apply Z.lt_le_incl. transitivity (Z.pos p2).
      assumption.
      rewrite <- N2Z.inj_pred by reflexivity. apply RY.
    apply Z.le_lt_trans with (m:=Z0). apply Z.opp_nonpos_nonneg.
      assumption.
      apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.

  (* x>0, y<0 *)
  rewrite <- Pos2Z.opp_pos, Z.rem_opp_r; [|discriminate]. split.
    transitivity Z0. apply Z.opp_nonpos_nonneg, Z.pow_nonneg. discriminate. assumption.
    apply Z.lt_le_trans with (m:=Z.pos p2).
      assumption.
      apply Z.opp_le_mono. rewrite N2Z.inj_pred, Pos2Z.opp_pos by reflexivity. apply RY.

  (* x<0, y<0 *)
  do 2 rewrite <- Pos2Z.opp_pos. rewrite Z.rem_opp_r,Z.rem_opp_l; try discriminate. split.
    apply -> Z.opp_le_mono. transitivity (Z.pos p1).
      apply Z.rem_le. apply Pos2Z.is_nonneg. apply Pos2Z.is_pos.
      apply Z.opp_le_mono. rewrite Pos2Z.opp_pos. apply RX.
    apply Z.le_lt_trans with (m:=Z0).
      apply Z.opp_nonpos_nonneg. assumption.
      apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Lemma mod_bound:
  forall w x y, x < 2^w -> y < 2^w -> x mod y < 2^w.
Proof.
  intros. destruct y as [|y].
    destruct x; assumption.
    etransitivity. apply N.mod_lt. discriminate 1. assumption.
Qed.

Lemma shiftl_bound:
  forall w x y, x < 2^w -> N.shiftl x y < 2^(w+y).
Proof.
  intros. rewrite N.shiftl_mul_pow2, N.pow_add_r. apply N.mul_lt_mono_pos_r.
    apply mp2_gt_0.
    assumption.
Qed.

Lemma shiftr_bound:
  forall w x y, x < 2^w -> N.shiftr x y < 2^(w-y).
Proof.
  intros. destruct (N.le_gt_cases y w).
    rewrite N.shiftr_div_pow2. apply N.Div0.div_lt_upper_bound.
      rewrite <- N.pow_add_r, N.add_sub_assoc, N.add_comm, N.add_sub; assumption.
    destruct x as [|x]. 
      rewrite N.shiftr_0_l. apply mp2_gt_0.
      rewrite N.shiftr_eq_0. apply mp2_gt_0. apply N.log2_lt_pow2.
        reflexivity.
        etransitivity. eassumption. apply N.pow_lt_mono_r. reflexivity. assumption.
Qed.

Lemma shiftr_low_pow2: forall a n, a < 2^n -> N.shiftr a n = 0.
Proof.
  intros. destruct a. apply N.shiftr_0_l.
  apply N.shiftr_eq_0. apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

Lemma ones_bound:
  forall w, N.ones w < 2^w.
Proof.
  intro. rewrite N.ones_equiv. apply N.lt_pred_l. apply N.pow_nonzero. discriminate 1.
Qed.

Lemma logic_op_bound:
  forall w n1 n2 f
         (Z: forall x y b (Z1: N.testbit x b = false) (Z2: N.testbit y b = false),
             N.testbit (f x y) b = false)
         (W1: n1 < 2^w) (W2: n2 < 2^w),
  f n1 n2 < 2^w.
Proof.
  intros. apply hibits_zero_bound. intros. apply Z;
    revert H; apply bound_hibits_zero; assumption.
Qed.

Lemma land_bound:
  forall w x y, x < 2^w -> N.land x y < 2^w.
Proof.
  intros. apply hibits_zero_bound. intros.
  erewrite N.land_spec, bound_hibits_zero; try eassumption. reflexivity.
Qed.

Lemma lor_bound:
  forall w x y, x < 2^w -> y < 2^w -> N.lor x y < 2^w.
Proof.
  intros. apply logic_op_bound; try assumption.
  intros. rewrite N.lor_spec, Z1, Z2. reflexivity.
Qed.

Lemma lxor_bound:
  forall w x y, x < 2^w -> y < 2^w -> N.lxor x y < 2^w.
Proof.
  intros. apply logic_op_bound; try assumption.
  intros. rewrite N.lxor_spec, Z1, Z2. reflexivity.
Qed.

Lemma lnot_bound:
  forall w x, x < 2^w -> N.lnot x w < 2^w.
Proof.
  intros. unfold N.lnot. apply lxor_bound. assumption.
  unfold N.ones. rewrite N.shiftl_1_l. apply N.lt_pred_l, N.pow_nonzero. discriminate 1.
Qed.

Lemma bit_bound:
  forall (b:bool), (if b then 1 else 0) < 2.
Proof. destruct b; reflexivity. Qed.

Lemma cast_high_bound:
  forall n w w', n < 2^w -> w' <= w -> N.shiftr n (w - w') < 2^w'.
Proof.
  intros. apply hibits_zero_bound. intros.
  rewrite N.shiftr_spec by apply N.le_0_l. apply (bound_hibits_zero w). assumption.
  rewrite N.add_sub_assoc, N.add_comm, <- N.add_sub_assoc by assumption.
  apply N.le_add_r.
Qed.

Lemma concat_bound:
  forall n1 n2 w1 w2, n1 < 2^w1 -> n2 < 2^w2 -> N.lor (N.shiftl n1 w2) n2 < 2^(w1+w2).
Proof.
  intros. apply lor_bound. apply shiftl_bound. assumption. eapply N.lt_le_trans.
    eassumption.
    apply N.pow_le_mono_r. discriminate 1. rewrite N.add_comm. apply N.le_add_r.
Qed.

End OpBounds.



Section BitOps.

Definition bitop_has_spec f g := forall a a' n, N.testbit (f a a') n = g (N.testbit a n) (N.testbit a' n).

Theorem bitop_mod_pow2:
  forall f g (SPEC: bitop_has_spec f g) (PZ: g false false = false),
  forall n1 n2 p, f n1 n2 mod 2^p = f (n1 mod 2^p) (n2 mod 2^p).
Proof.
  intros. rewrite <- !N.land_ones. apply N.bits_inj. intro i. rewrite N.land_spec, !SPEC, !N.land_spec.
  destruct (N.le_gt_cases p i).
    rewrite N.ones_spec_high, !Bool.andb_false_r by assumption. symmetry. apply PZ.
    rewrite N.ones_spec_low, !Bool.andb_true_r by assumption. reflexivity.
Qed.

Definition N_land_mod_pow2 := bitop_mod_pow2 N.land andb N.land_spec (eq_refl false).
Definition N_lor_mod_pow2 := bitop_mod_pow2 N.lor orb N.lor_spec (eq_refl false).
Definition N_lxor_mod_pow2 := bitop_mod_pow2 N.lxor xorb N.lxor_spec (eq_refl false).

Theorem N_land_mod_pow2_move:
  forall p x y, N.land (x mod 2^p) y = N.land x (y mod 2^p).
Proof.
  intros.
  rewrite <- N.land_ones, <- N.land_assoc, (N.land_comm _ y), N.land_ones.
  reflexivity.
Qed.

Theorem N_land_mod_pow2_moveout:
  forall p x y, N.land x (y mod 2^p) = (N.land x y) mod 2^p.
Proof.
  intros.
  rewrite N.land_comm, <- N.Div0.mod_mod, N_land_mod_pow2_move, N.land_comm.
  symmetry. apply N_land_mod_pow2.
Qed.

Theorem land_mod_min:
  forall p x y, N.land x (y mod 2^p) = N.land (x mod 2^(N.min (N.size y) p)) y.
Proof.
  intros.
  rewrite <- (N.mod_small y (2^N.size y)) at 1 by apply N.size_gt.
  rewrite mp2_mod_mod_min.
  symmetry. apply N_land_mod_pow2_move.
Qed.

Theorem size_le_diag:
  forall n, N.size n <= n.
Proof.
  destruct n as [|p]. discriminate. change (Pos.size p <= p)%positive.
  induction p.
    simpl. etransitivity.
      apply -> Pos.succ_le_mono. apply IHp.
      rewrite Pos.xI_succ_xO, <- Pos.add_diag. apply -> Pos.succ_le_mono. apply Pos.lt_le_incl, Pos.lt_add_r.
    simpl. etransitivity.
      apply -> Pos.succ_le_mono. apply IHp.
      rewrite <- Pos.add_1_r, <- Pos.add_diag. apply Pos.add_le_mono_l, Pos.le_1_l.
    reflexivity.
Qed.

Theorem Pos_popcount_bound:
  forall p, (Pos_popcount p <= Pos.size p)%positive.
Proof.
  induction p.
    apply -> Pos.succ_le_mono. assumption.
    etransitivity.
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
      apply -> Pos.succ_le_mono. assumption.
    reflexivity.
Qed.

Theorem popcount_bound:
  forall n, popcount n <= N.size n.
Proof.
  destruct n. reflexivity. apply Pos_popcount_bound.
Qed.

Theorem popcount_0:
  forall n, popcount n = 0 -> n = 0.
Proof.
  intros. destruct n. reflexivity. discriminate.
Qed.

Theorem popcount_pos:
  forall n, 0 < popcount n <-> 0 < n.
Proof.
  intro. split; intro; (destruct n; [ discriminate | reflexivity ]).
Qed.

Theorem popcount_bit:
  forall n, popcount n = n <-> n < 2.
Proof.
  split; intro.

    destruct n as [|n]. reflexivity.
    rewrite <- (N.succ_pred (N.pos n)) in * by discriminate 1. destruct (N.pred _) as [|p]. reflexivity.
    rewrite <- (N.succ_pred (N.pos p)) in * by discriminate 1. destruct (N.pred _) as [|q]. discriminate.
    clear n p. contradict H. apply N.lt_neq.
    eapply N.le_lt_trans. apply popcount_bound.
    rewrite N.size_log2 by apply N.neq_succ_0. apply -> N.succ_lt_mono. apply N.lt_succ_r.
    induction q using Pos.peano_ind.
      discriminate 1.
      etransitivity.
        apply N.log2_succ_le.
        apply (proj1 (N.succ_le_mono _ (N.pos q))). etransitivity.
          apply IHq.
          reflexivity.

    destruct n as [|[n|n|]]; try reflexivity; destruct n; discriminate.
Qed.

Theorem popcount_double:
  forall n, popcount (N.double n) = popcount n.
Proof.
  destruct n; reflexivity.
Qed.

Theorem popcount_succ_double:
  forall n, popcount (N.succ_double n) = N.succ (popcount n).
Proof.
  destruct n; reflexivity.
Qed.

Theorem popcount_div2':
  forall n, popcount n = popcount (N.div2 n) + n mod 2.
Proof.
  intro. change 2 with (2^1). rewrite <- N.land_ones.
  destruct n as [|[p|p|]]; try reflexivity.
  simpl. rewrite Pos.add_1_r. reflexivity.
Qed.

Theorem popcount_div2:
  forall n, popcount (N.div2 n) = popcount n - n mod 2.
Proof.
  intro. eapply N.add_cancel_r. rewrite N.sub_add.
    symmetry. apply popcount_div2'.
    destruct n as [|n]. discriminate 1. transitivity 1.
      apply (N.lt_le_pred _ 2), N.mod_lt. discriminate 1.
      apply (N.le_succ_l 0), popcount_pos. reflexivity.
Qed.

Theorem popcount_lor_land:
  forall m n, popcount (N.lor m n) + popcount (N.land m n) = popcount m + popcount n.
Proof.
  apply N_bitwise_ind2. reflexivity. intros.
  rewrite (popcount_div2' m), (popcount_div2' n).
  rewrite N.add_shuffle1. rewrite <- IH.
  rewrite !N.div2_spec. rewrite <- N.shiftr_lor, <- N.shiftr_land. rewrite <- !N.div2_spec.
  replace (m mod 2 + n mod 2) with (N.lor m n mod 2 + N.land m n mod 2).
    rewrite <- N.add_shuffle1. rewrite <- !popcount_div2'. reflexivity.
    rewrite (N_lor_mod_pow2 _ _ 1), (N_land_mod_pow2 _ _ 1), <- !N.bit0_mod.
      do 2 destruct N.testbit; reflexivity.
Qed.

Corollary popcount_lor:
  forall m n, popcount (N.lor m n) = popcount m + popcount n - popcount (N.land m n).
Proof.
  intros. rewrite <- popcount_lor_land, N.add_sub. reflexivity.
Qed.

Corollary popcount_land:
  forall m n, popcount (N.land m n) = popcount m + popcount n - popcount (N.lor m n).
Proof.
  intros. rewrite <- popcount_lor_land, N.add_comm, N.add_sub. reflexivity.
Qed.

Theorem popcount_land_bound:
  forall m n, popcount (N.land m n) <= N.min (popcount m) (popcount n).
Proof.
  assert (B: forall b, b mod 2^1 = 0 \/ b mod 2^1 = 1).
    intro. apply N.le_1_r, (N.lt_le_pred _ 2), N.mod_lt. discriminate.
  assert (H: forall m n, popcount (N.land m n) <= popcount m).
    apply N_bitwise_ind2. reflexivity. intros.
    rewrite popcount_div2, !N.div2_spec, <- N.shiftr_land, <- N.div2_spec, popcount_div2 in IH.
    apply N.le_sub_le_add_r in IH. etransitivity. exact IH.
    change 2 with (2^1). rewrite <- N.add_sub_swap.

      apply N.le_sub_le_add_r, N.add_le_mono_l. rewrite N_land_mod_pow2.
      destruct (B m) as [H1|H1], (B n) as [H2|H2]; rewrite H1, H2; discriminate 1.

      specialize (B m). destruct B; rewrite H.
        apply N.le_0_l.
        apply (N.le_succ_l 0), popcount_pos. destruct m. discriminate. reflexivity.

  intros. apply N.min_glb. apply H. rewrite N.land_comm. apply H.
Qed.

Theorem popcount_shiftl:
  forall n i, popcount (N.shiftl n i) = popcount n.
Proof.
  induction i using N.peano_ind.
    rewrite N.shiftl_0_r. reflexivity.
    rewrite N.shiftl_succ_r. rewrite popcount_double. apply IHi.
Qed.

Corollary popcount_pow2:
  forall n, popcount (2^n) = 1.
Proof.
  intros. rewrite <- N.shiftl_1_l, popcount_shiftl. reflexivity.
Qed.

Theorem popcount_shiftr':
  forall n i, popcount n = popcount (N.shiftr n i) + popcount (n mod 2^i).
Proof.
  intros.
  rewrite <- (N.lor_ldiff_and n (N.ones i)) at 1.
  rewrite popcount_lor.
  rewrite N.land_comm, N.land_assoc, N.land_ldiff, N.sub_0_r.
  rewrite N.land_comm, N.land_ones.
  rewrite N.ldiff_ones_r, popcount_shiftl.
  reflexivity.
Qed.

Corollary popcount_shiftr:
  forall n i, popcount (N.shiftr n i) = popcount n - popcount (n mod 2^i).
Proof.
  intros. rewrite (popcount_shiftr' n i), N.add_sub. reflexivity.
Qed.

Theorem popcount_ones:
  forall n, popcount (N.ones n) = n.
Proof.
  induction n using N.peano_ind. reflexivity.
  rewrite <- N.add_1_r, N.ones_add, N.mul_1_r.
  assert (H: N.land (2^n) (N.ones n) = 0).
    erewrite <- N.shiftl_1_l, <- mp2_div_same, <- N.shiftr_div_pow2, <- N.ldiff_ones_r.
    apply N.land_ldiff.
  rewrite N.add_nocarry_lxor, N.lxor_lor by exact H.
  rewrite popcount_lor, H, N.sub_0_r, popcount_pow2, IHn.
  apply N.add_comm.
Qed.

Theorem popcount_ldiff_land:
  forall m n, popcount (N.ldiff m n) + popcount (N.land m n) = popcount m.
Proof.
  apply N_bitwise_ind2. reflexivity. intros.
  rewrite (popcount_div2' (N.ldiff _ _)), (popcount_div2' (N.land _ _)).
  rewrite !N.div2_spec, N.shiftr_ldiff, N.shiftr_land, <- !N.div2_spec.
  rewrite N.add_shuffle1, IH.
  symmetry. etransitivity. apply popcount_div2'. apply f_equal.
  rewrite <- !N.bit0_mod, N.ldiff_spec, N.land_spec.
  do 2 destruct N.testbit; reflexivity.
Qed.

Corollary popcount_ldiff:
  forall m n, popcount (N.ldiff m n) = popcount m - popcount (N.land m n).
Proof.
  intros. symmetry. eapply N.add_cancel_r. rewrite popcount_ldiff_land. apply N.sub_add.
  etransitivity. apply popcount_land_bound. apply N.le_min_l.
Qed.

Theorem popcount_bitmap:
  forall f m n (H: forall i (H: N.testbit m i = true),
                   N.testbit n (f i) = true /\ (forall j, f i = f j -> i = j)),
  popcount m <= popcount n.
Proof.
  intros f m. revert f. induction m using N.binary_ind; intros.
    apply N.le_0_l.
    rewrite popcount_double. apply (IHm (fun k => f (N.succ k))). intros. split.
      apply H. rewrite N.double_spec, N.double_bits_succ. assumption.
      intros. apply N.succ_inj. apply H.
        rewrite N.double_spec, N.double_bits_succ. assumption.
        assumption.
    replace (popcount n) with (N.succ (popcount (N.clearbit n (f 0)))).
      rewrite popcount_succ_double. apply -> N.succ_le_mono. apply (IHm (fun k => f (N.succ k))). split.
        replace (N.testbit _ _) with (N.testbit n (f (N.succ i))).
          apply H. rewrite N.succ_double_spec, N.testbit_odd_succ by apply N.le_0_l. assumption.
          symmetry. apply N.clearbit_neq. intro H1. apply (N.neq_succ_0 i), H.
            rewrite N.succ_double_spec, N.testbit_odd_succ by apply N.le_0_l. assumption.
            symmetry. assumption.
        intros. apply N.succ_inj. apply H.
          rewrite N.succ_double_spec, N.testbit_odd_succ by apply N.le_0_l. assumption.
          assumption.
      rewrite N.clearbit_spec', <- N.add_1_r, <- (popcount_pow2 (f 0)). replace (2^_) with (N.land n (2^f 0)) at 2.
        apply popcount_ldiff_land.
        apply N.bits_inj. intro i. rewrite N.land_spec, N.pow2_bits_eqb. destruct (_ =? _) eqn:H1.
          rewrite Bool.andb_true_r. apply N.eqb_eq in H1. subst i. rewrite N.succ_double_spec in H. apply (H 0 (N.testbit_odd_0 _)).
          apply Bool.andb_false_r.
Qed.

Theorem popcount_parity_lxor:
  forall m n, N.even (popcount (N.lxor m n)) = N.even (popcount m + popcount n).
Proof.
  intros. pattern m, n. apply N_bitwise_ind2; intros. reflexivity.
  clear m n. rename m0 into m, n0 into n.
  rewrite (popcount_div2' m), (popcount_div2' n), N.add_shuffle1.
  rewrite N.even_add, <- IH.
  replace (N.even (_+_)) with (N.even (popcount (N.lxor m n mod 2))).
    rewrite <- N.even_add, !N.div2_spec, <- N.shiftr_lxor, <- popcount_shiftr'. reflexivity.
    rewrite <- !N.bit0_mod, N.lxor_spec. do 2 destruct N.testbit; reflexivity.
Qed.

Definition parity8 n :=
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1.

Theorem parity8_byte:
  forall n, parity8 n = parity8 (n mod 2^8).
Proof.
  intro. unfold parity8. rewrite <- !N.land_ones.
  apply f_equal2; [|reflexivity].
  apply N.bits_inj. intro i.
  repeat rewrite !N.land_spec, ?N.lxor_spec, ?N.shiftr_spec'. rewrite !N_ones_spec_ltb.
  destruct i.
    rewrite !Bool.andb_true_r. reflexivity.
    replace (N.pos p <? 1) with false.
      rewrite !Bool.andb_false_r. reflexivity.
      destruct p; reflexivity.
Qed.

Theorem parity8_popcount:
  forall n, parity8 n = N.b2n (N.even (popcount (n mod 2^8))).
Proof.
  assert (H1: forall n i, xorb (N.testbit n i) (N.odd (popcount (n mod 2^i)))
                          = N.odd (popcount (n mod 2^(N.succ i)))).
    intros. rewrite (popcount_shiftr' (n mod 2^N.succ i) i), N.odd_add.
    rewrite mp2_mod_mod_min, N.min_r by apply N.le_succ_diag_r.
    rewrite testbit_xbits, <- xbits_equiv.
    rewrite (proj2 (popcount_bit (xbits _ _ _))).
      reflexivity.
      replace 2 with (2^(N.succ i - i)).
        apply xbits_bound.
        rewrite N.sub_succ_l, N.sub_diag by reflexivity. reflexivity.

  set (f x i := N.lxor (N.shiftr x i) x).
  assert (H2: forall x i j, N.testbit (f x i) j = xorb (N.testbit x (j+i)) (N.testbit x j)).
    intros. unfold f. rewrite N.lxor_spec, N.shiftr_spec'. reflexivity.

  intro. rewrite parity8_byte. set (n8 := n mod _).
  unfold parity8. fold (f n8 4) (f (f n8 4) 2) (f (f (f n8 4) 2) 1).
  rewrite <- N.bit0_mod, !H2, !Bool.xorb_assoc. simpl.
  repeat match goal with |- context [ xorb (N.testbit ?n ?i) (xorb (N.testbit ?n ?j) ?e) ] =>
    lazymatch eval compute in (i <? j) with false => fail | true =>
      rewrite <- (Bool.xorb_assoc (N.testbit n i) (N.testbit n j) e),
              (Bool.xorb_comm (N.testbit n i) (N.testbit n j)), Bool.xorb_assoc
    end
  end.
  replace (N.testbit n8 0) with (N.odd (popcount (n8 mod 2^N.succ 0))).
    rewrite !H1, <- N.negb_even. simpl. subst n8. rewrite N.Div0.mod_mod.
      destruct N.even; reflexivity.
    rewrite <- N.bit0_mod. destruct N.testbit; reflexivity.
Qed.

End BitOps.



Section Traces.

(* This is like nth_error except it recurses on l, for easier inductions on lists. *)
Fixpoint ith {A} (l:list A) (i:nat) {struct l} :=
  match l with nil => None | h::t =>
    match i with O => Some h | S j => ith t j end
  end.

Theorem ith_cons {A}:
  forall (a:A) l i, ith (a::l) (S i) = ith l i.
Proof. reflexivity. Qed.

Theorem ith_nth_error: @ith = @nth_error.
Proof.
  extensionality A. extensionality l. induction l; extensionality i.
    destruct i; reflexivity.
    destruct i. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Theorem ith_skipn_hd {A}:
  forall (l:list A) i, ith l i = hd_error (skipn i l).
Proof.
  induction l; intros.
    rewrite skipn_nil. reflexivity.
    destruct i.
      reflexivity.
      apply IHl.
Qed.

Theorem ith_In {A}:
  forall (l:list A) i x, ith l i = Some x -> In x l.
Proof. rewrite ith_nth_error. apply nth_error_In. Qed.

Theorem In_ith {A}:
  forall l (x:A), In x l -> exists i, ith l i = Some x.
Proof. rewrite ith_nth_error. apply In_nth_error. Qed.

Theorem ith_None {A}:
  forall (l:list A) i, ith l i = None <-> (length l <= i)%nat.
Proof. rewrite ith_nth_error. apply nth_error_None. Qed.

Theorem ith_Some {A}:
  forall (l:list A) i, ith l i <> None <-> (i < length l)%nat.
Proof. rewrite ith_nth_error. apply nth_error_Some. Qed.

Theorem ith_nth {A}:
  forall l i (x d:A), ith l i = Some x -> nth i l d = x.
Proof. rewrite ith_nth_error. apply nth_error_nth. Qed.

Theorem ith_nth' {A}:
  forall l i (d:A), (i < length l)%nat -> ith l i = Some (nth i l d).
Proof. rewrite ith_nth_error. apply nth_error_nth'. Qed.

Theorem ith_app1 {A}:
  forall (l l':list A) i, (i < length l)%nat -> ith (l++l') i = ith l i.
Proof. rewrite ith_nth_error. apply nth_error_app1. Qed.

Theorem ith_app2 {A}:
  forall (l l':list A) i, (length l <= i)%nat -> ith (l++l') i = ith l' (i - length l).
Proof. rewrite ith_nth_error. apply nth_error_app2. Qed.

Theorem ith_map {A B}:
  forall (f: A -> B) i l, ith (map f l) i = option_map f (ith l i).
Proof. rewrite ith_nth_error. apply nth_error_map. Qed.

Theorem map_ith {A B}:
  forall (f: A -> B) i l d, ith l i = Some d -> ith (map f l) i = Some (f d).
Proof. rewrite ith_nth_error. apply map_nth_error. Qed.

Theorem ith_split {A}:
  forall l i (a:A), ith l i = Some a -> exists l1 l2, l = l1++a::l2 /\ length l1 = i.
Proof. rewrite ith_nth_error. apply nth_error_split. Qed.

Theorem ith_repeat {A}:
  forall (a:A) n i, (i < n)%nat -> ith (repeat a n) i = Some a.
Proof. rewrite ith_nth_error. apply nth_error_repeat. Qed.

Theorem ith_middle {A}:
  forall l l' (a:A), ith (l ++ a :: l') (length l) = Some a.
Proof.
  intros. rewrite ith_app2, Nat.sub_diag; reflexivity.
Qed.

Theorem NoDup_ith {A}:
  forall (l: list A), NoDup l <->
   (forall i j, (i < length l)%nat -> ith l i = ith l j -> i = j).
Proof. rewrite ith_nth_error. apply NoDup_nth_error. Qed.

Theorem ith_ext {A}:
  forall (l1 l2:list A), (forall i, ith l1 i = ith l2 i) -> l1 = l2.
Proof.
  induction l1; intros.
    destruct l2. reflexivity. specialize (H O). discriminate.
    destruct l2.
      specialize (H O). discriminate.
      injection (H O). intro. subst. apply f_equal. apply IHl1. intro. apply (H (S i)).
Qed.

Theorem ith_tl {A}:
  forall (l:list A) i, ith (tl l) i = ith l (S i).
Proof.
  intros. destruct l; reflexivity.
Qed.

Theorem ith_app {A}:
  forall (l1 l2:list A) i,
  ith (l1 ++ l2) i = ith (if i <? length l1 then l1 else l2)%nat
                         (if i <? length l1 then i else i - length l1)%nat.
Proof.
  intros. rewrite !ith_nth_error. destruct Nat.ltb eqn:H.
    apply nth_error_app1, Nat.ltb_lt, H.
    apply nth_error_app2, Nat.ltb_ge, H.
Qed.

Theorem ith_removelast {A}:
  forall (l:list A) i,
  ith (removelast l) i = if (S i =? length l)%nat then None else ith l i.
Proof.
  induction l; intro.
    reflexivity.
    destruct l.
      destruct i; reflexivity.
      destruct i.
        reflexivity.
        change (removelast _) with (a::removelast (a0::l)). rewrite ith_cons, IHl. reflexivity.
Qed.

Theorem ith_rev {A}:
  forall (l:list A) i,
  (i < length l)%nat -> ith (rev l) i = ith l (length l - S i).
Proof.
  induction l; intros.
  contradict H. apply Nat.nlt_0_r.
  simpl in H. apply (proj1 (Nat.lt_succ_r _ _)), Nat.le_lteq in H. destruct H.

    simpl length.
    rewrite Nat.sub_succ_l, ith_cons by apply Nat.le_succ_l, H.
    simpl. rewrite ith_app1 by (rewrite ?length_rev; assumption).
    apply IHl, H.

    rewrite H. simpl. rewrite ith_app, length_rev, Nat.ltb_irrefl, Nat.sub_diag. reflexivity.
Qed.

Theorem length_remove {A}:
  forall eq (a:A) l, (length (remove eq a l) + count_occ eq l a)%nat = length l.
Proof.
  induction l. reflexivity.
  simpl. do 2 destruct eq; subst; try contradiction.
    rewrite Nat.add_succ_r, IHl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem ith_remove {A}:
  forall eq (a:A) l i, ith l i <> Some a ->
  ith (remove eq a l) (i - count_occ eq (firstn i l) a) = ith l i.
Proof.
  induction l; intros. reflexivity.
  simpl. destruct i as [|i].
    rewrite Nat.sub_0_l. destruct eq.
      subst a0. contradict H. reflexivity.
      reflexivity.
    simpl count_occ. destruct eq.
      subst a0. destruct eq; [|contradiction]. rewrite Nat.sub_succ. apply IHl. assumption.
      destruct eq. subst a0. contradiction. rewrite Nat.sub_succ_l.
        apply IHl. assumption.
        etransitivity. apply count_occ_bound. apply firstn_le_length.
Qed.

Theorem length_concat {A}:
  forall (l:list (list A)),
  length (concat l) = fold_left (fun n a => n + length a)%nat l O.
Proof.
  intros. rewrite <- (Nat.add_0_l (length _)). generalize O.
  induction l; intro. apply Nat.add_0_r.
  simpl. rewrite length_app. rewrite <- IHl. apply Nat.add_assoc.
Qed.

Theorem ith_concat1 {A}:
  forall (l1:list A) t i,
  (i < length l1)%nat -> ith (concat (l1::t)) i = ith l1 i.
Proof.
  intros. simpl. apply ith_app1. assumption.
Qed.

Theorem ith_concat2 {A}:
 forall (l:list (list A)) i n,
   (length (concat (firstn n l)) <= i)%nat ->
 ith (concat l) i = ith (concat (skipn n l)) (i - length (concat (firstn n l))).
Proof.
  intros.
  rewrite <- (firstn_skipn n l) at 1. rewrite concat_app. apply ith_app2, H.
Qed.

Theorem ith_split_l {A B}:
  forall (l:list (A*B)) i,
  ith (fst (split l)) i = option_map fst (ith l i).
Proof.
  induction l; intro. reflexivity.
  destruct i as [|i]; simpl; destruct a, split.
    reflexivity.
    apply IHl.
Qed.

Theorem ith_split_r {A B}:
  forall (l:list (A*B)) i,
  ith (snd (split l)) i = option_map snd (ith l i).
Proof.
  induction l; intro. reflexivity.
  destruct i as [|i]; simpl; destruct a, split.
    reflexivity.
    apply IHl.
Qed.

Definition option_map2 {A B C} (f: A -> B -> C) o1 o2 :=
  match o1 with None => None | Some a => option_map (f a) o2 end.

Theorem option_map2_none_r {A B C}:
  forall (f: A -> B -> C) o, option_map2 f o None = None.
Proof. destruct o; reflexivity. Qed.

Theorem ith_combine {A B}:
  forall (l l':list (A*B)) i,
  ith (combine l l') i = option_map2 pair (ith l i) (ith l' i).
Proof.
  induction l; intros. reflexivity.
  destruct l' as [|b l']. simpl. symmetry. apply option_map2_none_r.
  destruct i as [|i]. reflexivity.
  simpl. apply IHl.
Qed.

Theorem ith_firstn {A}:
  forall (l:list A) n i,
  ith (firstn n l) i = if (i <? n)%nat then ith l i else None.
Proof.
  induction l; intros.
    rewrite firstn_nil. destruct (_ <? _)%nat; reflexivity.
    destruct n as [|n].
      reflexivity.
      destruct i as [|i].
        reflexivity.
        simpl. replace (S i <? S n)%nat with (i <? n)%nat.
          apply IHl.
          destruct (i <? n)%nat eqn:H; symmetry.
            apply Nat.ltb_lt. apply -> Nat.succ_lt_mono. apply Nat.ltb_lt, H.
            apply Nat.ltb_ge. apply -> Nat.succ_le_mono. apply Nat.ltb_ge, H.
Qed.

Theorem ith_skipn {A}:
  forall (l:list A) n i,
  ith (skipn n l) i = ith l (n + i).
Proof.
  induction l; intros.
    rewrite skipn_nil. reflexivity.
    destruct n as [|n].
      reflexivity.
      apply IHl.
Qed.

Theorem Forall_ith:
  forall {A} (P:A->Prop) l, Forall P l <->
  (forall i, match ith l i with None => True | Some x => P x end).
Proof.
  split; intros.

    destruct (ith l i) eqn:H'; [|reflexivity].
    apply Forall_forall with (P:=P) (l:=l). assumption.
    eapply ith_In. eassumption.

    apply Forall_forall. intros x IN.
    apply In_ith in IN. destruct IN as [i IN].
    specialize (H i). rewrite IN in H. assumption.
Qed.

Theorem skipn_all3 {A}:
  forall n (l:list A), skipn n l = nil -> (length l <= n)%nat.
Proof.
  induction n; intros.
    rewrite skipn_O in H. subst. reflexivity.
    destruct l.
      apply Nat.le_0_l.
      simpl. apply le_n_S, IHn, H.
Qed.

Theorem stepsof_cons {A}:
  forall (x y:A) t, stepsof (x::y::t) = (x,y)::stepsof (y::t).
Proof. reflexivity. Qed.

Theorem ith_stepsof {A}:
  forall (l:list A) i,
  ith (stepsof l) i = match skipn i l with x::y::_ => Some (x,y) | _ => None end.
Proof.
  intros. revert l. induction i; intros.
    destruct l as [|? [|]]; reflexivity.
    destruct l. reflexivity. simpl skipn. rewrite <- IHi. destruct l.
      destruct i; reflexivity.
      reflexivity.
Qed.

Theorem length_cons {A}:
  forall l (a:A), length (a::l) = S (length l).
Proof. reflexivity. Qed.

Theorem length_stepsof {A}:
  forall (l:list A), length (stepsof l) = Nat.pred (length l).
Proof.
  induction l.
    reflexivity.
    destruct l as [|b l].
      reflexivity.
      rewrite stepsof_cons, !length_cons, IHl, length_cons, !Nat.pred_succ. reflexivity.
Qed.

Theorem rev_cons {A}:
  forall l (a:A), rev (a::l) = rev l ++ a :: nil.
Proof. reflexivity. Qed.

Theorem split_subtraces:
  forall T (h1 h2:T) t1 t2, h1::t1++h2::t2 = (h1::t1++h2::nil)++t2.
Proof.
  intros. simpl. rewrite <- List.app_assoc. reflexivity.
Qed.

Theorem startof_niltail {A}:
  forall t (a d:A), startof (t ++ a :: nil) d = a.
Proof. apply last_last. Qed.

Theorem startof_cons_cons {A}:
  forall (a b:A) t d, startof (a::b::t) d = startof (b::t) d.
Proof. reflexivity. Qed.

Theorem startof_nonnil {A}:
  forall (a d1 d2:A) t, startof (a::t) d1 = startof (a::t) d2.
Proof.
  intros. revert a. induction t; intro.
    reflexivity.
    rewrite !startof_cons_cons. apply IHt.
Qed.

Theorem startof_cons {A}:
  forall (a d:A) t, startof (a::t) d = startof t a.
Proof.
  intros. destruct t.
    reflexivity.
    rewrite startof_cons_cons. apply startof_nonnil.
Qed.

Theorem startof_hdrev {A}:
  forall t (d:A), startof t d = hd d (rev t).
Proof.
  intros. rewrite <- (rev_involutive t) at 1. destruct (rev t).
    reflexivity.
    rewrite rev_cons, startof_niltail. reflexivity.
Qed.

Theorem startof_rev {A}:
  forall t (a:A), startof (rev t) a = hd a t.
Proof.
  intros. rewrite startof_hdrev, rev_involutive. reflexivity.
Qed.

Theorem ostartof_niltail {A}:
  forall t (a:A), ostartof (t ++ a :: nil) = Some a.
Proof.
  intros. destruct t.
    reflexivity.
    simpl. rewrite startof_niltail. reflexivity.
Qed.

Theorem startof_app {A}:
  forall (a d:A) t1 t2, startof (t1++a::t2) d = startof t2 a.
Proof.
  intros. revert a d. induction t1; intros.
    apply startof_cons.
    simpl (_++_). rewrite startof_cons. apply IHt1.
Qed.

Theorem startof_prefix {A}:
  forall (xs xs':A) t t1 t2 (SPL: xs'::t = t2++xs::t1),
  startof t xs' = startof t1 xs.
Proof.
  intros. rewrite <- startof_cons with (d:=xs'). rewrite SPL.
  apply startof_app.
Qed.

Theorem ostartof_cons {A}:
  forall (a:A) t, ostartof (a::t) = Some (startof t a).
Proof. reflexivity. Qed.

Theorem ostartof_app {A}:
  forall (a:A) t1 t2, ostartof (t1++a::t2) = ostartof (a::t2).
Proof.
  intros. destruct t1.
    reflexivity.
    simpl. rewrite startof_app. reflexivity.
Qed.

Theorem rev_destruct {A}:
  forall (l:list A), {l=nil}+{exists l' a, l = l' ++ a :: nil}.
Proof.
  induction l.
    left. reflexivity.
    right. destruct IHl.
      subst. exists nil,a. reflexivity.
      destruct e as [l' [a1 H]]. subst. exists (a::l'),a1. reflexivity.
Qed.

Theorem stepsof_app {A}:
  forall (l2 l1: list A),
    stepsof (l2++l1) = (stepsof l2) ++
                       match option_map2 pair (ostartof l2) (hd_error l1) with None => nil | Some xy => xy::nil end ++
                       (stepsof l1).
Proof.
  intros.
  destruct l1 as [|x l1']. simpl. rewrite option_map2_none_r, !app_nil_r. reflexivity.
  destruct (rev_destruct l2). subst. reflexivity. destruct e as [l2' [y H]]. subst.
  apply ith_ext. intro.
  rewrite ith_app, ith_stepsof, !skipn_app, length_stepsof, last_length, Nat.pred_succ, ostartof_niltail.
  destruct (_ <? _)%nat eqn:H1.
    rewrite ith_stepsof, skipn_app, !(proj2 (Nat.sub_0_le i _)), !skipn_O.
      destruct (skipn i l2') as [|a [|b l2'']] eqn:H; [|reflexivity..].
        apply skipn_all3 in H. contradict H. apply Nat.lt_nge, Nat.ltb_lt, H1.
      apply Nat.lt_le_incl, Nat.lt_lt_succ_r, Nat.ltb_lt, H1.
      apply Nat.lt_le_incl, Nat.ltb_lt, H1.
    apply Nat.ltb_ge, Nat.le_lteq in H1. destruct H1 as [H1|H1]; cycle 1.
      rewrite <- H1, Nat.sub_diag, skipn_all, (proj2 (Nat.sub_0_le _ _)).
        reflexivity.
        apply Nat.le_succ_diag_r.
      cbn - [ith stepsof]. rewrite 2!skipn_all2.
        destruct i.
          contradict H1. apply Nat.nlt_0_r.
          rewrite Nat.sub_succ, Nat.sub_succ_l, ith_cons, ith_stepsof.
            reflexivity.
            apply Nat.lt_succ_r, H1.
        apply Nat.le_add_le_sub_r, Nat.le_succ_l, H1.
        apply Nat.lt_le_incl, H1.
Qed.

Inductive ForallPrefixes {A} (P: list A -> Prop) : list A -> Prop :=
| ForallPrefixes_nil: P nil -> ForallPrefixes P nil
| ForallPrefixes_cons (x:A) (l:list A): P (x::l) -> ForallPrefixes P l -> ForallPrefixes P (x::l).

Theorem forallprefixes_app {A}:
  forall P (t1 t2:list A) (FA: ForallPrefixes P (t1++t2)),
  ForallPrefixes P t2.
Proof.
  induction t1; intros.
    assumption.
    apply IHt1. inversion FA. assumption.
Qed.

Theorem forallprefixes_nil_inv {A}:
  forall P (t: list A) (FA: ForallPrefixes P t),
  P nil.
Proof.
  intros.
  rewrite <- (app_nil_r t) in FA. apply forallprefixes_app in FA.
  inversion FA. assumption.
Qed.

End Traces.


Section InvariantMaps.

(* Sometimes we want to assert that an invariant is present and satisfied, while other times we
   want to more leniently stipulate that an invariant is satisfied if present: *)
Definition true_inv i := match i with Some P => P | None => False end.
Definition trueif_inv i := match i with Some P => P | None => True end.
Definition get_precondition {S T} (p: S -> _ -> option T) Invs (xp: _ -> bool) a1 (s1:S) t1 : option Prop :=
  if xp ((Addr a1,s1)::t1) then None
  else if p s1 a1 then Invs ((Addr a1,s1)::t1) else None.
Definition get_postcondition {S T} (p: S -> _ -> option T) Invs (xp: _ -> bool) a1 (s1:S) t1 : option Prop :=
  if xp ((Addr a1,s1)::t1) then if p s1 a1 then
    Some match Invs ((Addr a1,s1)::t1) with Some P => P | None => True end
  else None else None.

Lemma trueif_true_inv: forall i, true_inv i -> trueif_inv i.
Proof. intros. destruct i. assumption. contradiction. Qed.

Lemma trueif_None: trueif_inv None -> True.
Proof. intro. exact I. Qed.

Lemma trueif_Some: forall P, trueif_inv (Some P) -> P.
Proof. intros. assumption. Qed.

Lemma trueinv_Some: forall P, true_inv (Some P) -> P.
Proof. intros. assumption. Qed.

Lemma trueinv_None: ~ true_inv None.
Proof. intro. assumption. Qed.

Definition unterminated {A} xp :=
  ForallPrefixes (fun (t:list A) => xp t = false).

Lemma unterminated_cons {A}:
  forall xp (a:A) t (H: xp (a::t) = false) (UT: unterminated xp t),
  unterminated xp (a::t).
Proof. intros. constructor; assumption. Qed.

Lemma unterminated_tl {A}:
  forall xp (a:A) t (UT: unterminated xp (a::t)), unterminated xp t.
Proof. intros. inversion UT. assumption. Qed.

End InvariantMaps.



(* Tactic "destruct_inv w PRE" divides the inductive case of prove_invs into subgoals,
   one for each invariant point defined by hypothesis H, and puts the goals in
   ascending order by address.  Argument w should be the max bitwidth of addresses to
   consider (e.g., 32 on 32-bit ISAs). *)

Ltac simpl_inv H a :=
  tryif (simple apply trueinv_None in H) then (exfalso; exact H)
  else tryif (apply trueinv_Some in H) then (hnf in H; shelve)
  else fail "unable to simplify" H "to an invariant for address" a.

Ltac shelve_case H :=
  lazymatch type of H with
  | true_inv (get_precondition _ _ _ ?a _ _) => simpl_inv H a
  | true_inv (get_postcondition _ _ _ ?a _ _) => simpl_inv H a
  | _ => fail "unable to simplify" H "to an invariant"
  end.

Ltac shelve_cases_loop H a :=
  let g := numgoals in do g (
    (only 1: (case a as [a|a|]; [| |shelve_case H]));
    (unshelve (only 2: shelve; cycle g));
    revgoals; cycle g; revgoals;
    cycle 1
  );
  try (first [ simple apply trueinv_None in H | apply trueinv_Some in H ]; exfalso; exact H).

Tactic Notation "shelve_cases" int_or_var(i) hyp(H) :=
  lazymatch type of H with
  | true_inv (get_precondition _ _ _ ?a _ _) =>
    is_var a; case a as [|a]; [ shelve_case H | do i shelve_cases_loop H a ];
    fail "bit width" i "is insufficient to explore the invariant space"
  | true_inv (get_postcondition _ _ _ ?a _ _) =>
    is_var a; case a as [|a]; [ shelve_case H | do i shelve_cases_loop H a ];
    fail "bit width" i "is insufficient to explore the invariant space"
  | _ => fail "hypothesis" H "is not a precondition of the form (true_inv (get_...condition ...))"
  end.

Tactic Notation "destruct_inv" int_or_var(i) hyp(H) :=
  unshelve (shelve_cases i H).

(* Tactic "focus_addr n" brings the goal for the invariant at address n
   to the head of the goal list. *)
Tactic Notation "focus_addr" constr(n) :=
  unshelve (lazymatch goal with |- _ _ ((Addr n, _)::_) => shelve
                              | _ => idtac end).


Section MemTheory.

(* The getmem/setmem memory accessors are defined as Peano recursions over N,
   rather than natural number recursions.  This is important for keeping proof
   terms small, but can make it more difficult to write inductive proofs.  To
   ease this burden, we here define machinery for inductively reasoning about
   getmem/setmem.

   Proofs that inductively expand getmem/setmem should typically perform the
   following steps:

   (1) Use Peano induction to induct over length argument:
         induction len using N.peano_ind.

   (2) Within the proof, unfold the base case (where len=0) using the getmem_0
       or setmem_0 theorems.

   (3) Unfold inductive cases (where len = N.succ _) using the getmem_succ
       or setmem_succ theorems. *)

(* The upper bound for the numeric representation of virtual memory is
   2^(2^w*8), which is a huge number that Coq must avoid expanding.
   We therefore create a special name for it here, allowing proof
   environments to set it Opaque. *)
Definition memsize w := 2^(2^w*8).

(* Base cases for getmem/setmem *)
Theorem getmem_0: forall w e m a, getmem w e N0 m a = N0.
Proof. reflexivity. Qed.

Theorem setmem_0: forall w e m a v, setmem w e N0 m a v = m.
Proof. reflexivity. Qed.

(* Unfold getmem/setmem by one byte (for inductive cases of proofs). *)
Theorem getmem_succ:
  forall w e len m a, getmem w e (N.succ len) m a =
    match e with BigE => N.lor (getmem w e len m (N.succ a)) (N.shiftl (getbyte m a w) (len*8))
               | LittleE => N.lor (getbyte m a w) (N.shiftl (getmem w e len m (N.succ a)) 8)
    end.
Proof.
  intros. unfold getmem. rewrite (N.recursion_succ (@eq (addr->N))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

Theorem setmem_succ:
  forall w e len m a v, setmem w e (N.succ len) m a v =
    match e with BigE => setmem w e len (setbyte m a (N.shiftr v (len*8)) w) (N.succ a) (v mod 2^(len*8))
               | LittleE => setmem w e len (setbyte m a v w) (N.succ a) (N.shiftr v 8)
    end.
Proof.
  intros. unfold setmem.
  rewrite (N.recursion_succ (@eq (N->addr->N->N))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

(* special cases for when getmem/setmem are applied to access a single memory byte *)
Corollary getmem_1: forall w e m a, getmem w e 1 m a = getbyte m a w.
Proof.
  intros. change 1 with (N.succ 0).
  rewrite getmem_succ, getmem_0, N.mul_0_l, N.shiftl_0_r, N.lor_0_l, N.lor_0_r.
  destruct e; reflexivity.
Qed.

Corollary setmem_1: forall w e m a v, setmem w e 1 m a v = setbyte m a v w.
Proof.
  intros.
  change 1 with (N.succ 0).
  rewrite setmem_succ, !setmem_0, N.mul_0_l, N.shiftr_0_r.
  destruct e; reflexivity.
Qed.

Theorem getbyte_bound:
  forall m a w, getbyte m a w < 2^8.
Proof.
  intros. rewrite <- (N.mul_1_l 8), <- (N.add_sub 1 (a mod 2^w)),
                  N.add_1_l, N.mul_sub_distr_r.
  apply xbits_bound.
Qed.

Theorem getmem_bound:
  forall w e len m a, getmem w e len m a < 2^(len*8).
Proof.
  induction len using N.peano_ind; intros.
    rewrite getmem_0. apply mp2_gt_0.
    rewrite getmem_succ. destruct e; apply lor_bound.
      eapply N.lt_le_trans. apply IHlen. apply N.pow_le_mono_r.
        discriminate 1.
        apply N.mul_le_mono_r, N.le_succ_diag_r.
      rewrite N.mul_succ_l, N.add_comm. apply shiftl_bound, getbyte_bound.
      eapply N.lt_le_trans.
        apply mp2_mod_lt.
        apply N.pow_le_mono_r. discriminate 1.
          rewrite <- N.mul_sub_distr_r, <- N.add_1_l, N.add_sub, <- N.add_1_l.
          apply N.mul_le_mono. apply N.le_add_r. reflexivity.
      rewrite N.mul_succ_l. apply shiftl_bound, IHlen.
Qed.

Theorem getbyte_mod_l:
  forall m a w, getbyte m (a mod 2^w) w = getbyte m a w.
Proof.
  intros. unfold getbyte. rewrite mp2_mod_mod. reflexivity.
Qed.

Theorem getbyte_mod_r:
  forall m a w, getbyte m a w mod 2^8 = getbyte m a w.
Proof. intros. apply N.mod_small, getbyte_bound. Qed.

Theorem getbyte_newwidth:
  forall w' m a w, a mod 2^w = a mod 2^w' ->
  getbyte m a w = getbyte m a w'.
Proof.
  intros. unfold getbyte. rewrite H. reflexivity.
Qed.

Theorem setbyte_newwidth:
  forall w' m a n w, a mod 2^w = a mod 2^w' ->
  setbyte m a n w = setbyte m a n w'.
Proof.
  intros. unfold setbyte. rewrite H. reflexivity.
Qed.

Theorem getmem_mod_l:
  forall w e len m a, getmem w e len m (a mod 2^w) = getmem w e len m a.
Proof.
  induction len using N.peano_ind; intros.
    reflexivity.

    rewrite !getmem_succ, getbyte_mod_l.
    rewrite <- IHlen, <- N.add_1_r, mp2_add_l, N.add_1_r, IHlen.
    reflexivity.
Qed.

Theorem getmem_mod_r:
  forall w e len m a, (getmem w e len m a) mod 2^(len*8) = getmem w e len m a.
Proof.
  intros. apply N.mod_small. apply getmem_bound.
Qed.

Theorem setbyte_mod_l:
  forall m a v w,
  setbyte m (a mod 2^w) v w = setbyte m a v w.
Proof.
  intros. unfold setbyte. rewrite mp2_mod_mod. reflexivity.
Qed.

Theorem setmem_mod_l:
  forall w e len m a v,
  setmem w e len m (a mod 2^w) v = setmem w e len m a v.
Proof.
  induction len using N.peano_ind; intros.
    rewrite !setmem_0. reflexivity.

    rewrite !setmem_succ, !setbyte_mod_l.
    rewrite <- N.add_1_r, <- !(IHlen _ (_+1)), mp2_add_l, N.add_1_r, !IHlen.
    reflexivity.
Qed.

Theorem setbyte_mod_r:
  forall m a v w,
  setbyte m a (v mod 2^8) w = setbyte m a v w.
Proof.
  intros. unfold setbyte. rewrite mp2_mod_mod. reflexivity.
Qed.

Theorem setmem_mod_r:
  forall w e len m a v,
  setmem w e len m a (v mod 2^(len*8)) = setmem w e len m a v.
Proof.
  induction len using N.peano_ind; intros.
    rewrite !setmem_0. reflexivity.
    rewrite !setmem_succ. destruct e.

      rewrite <- xbits_equiv. unfold xbits.
      rewrite <- N.mul_sub_distr_r, <- N.add_1_l, N.add_sub, N.mul_1_l at 1.
      rewrite setbyte_mod_r, mp2_mod_mod_min, N.min_r. reflexivity.
      apply N.mul_le_mono_r, N.le_succ_diag_r.

      rewrite <- setbyte_mod_r, mp2_mod_mod_min, N.min_r, setbyte_mod_r.
        rewrite <- xbits_equiv. unfold xbits. rewrite N.mul_comm, <- N.mul_pred_r, N.pred_succ, N.mul_comm. apply IHlen.
        rewrite N.mul_succ_l. apply N.le_add_l.
Qed.

(* Break an (i+j)-byte number read/stored to/from memory into two numbers of size i and j. *)
Theorem getmem_split:
  forall w e i j m a, getmem w e (i+j) m a =
    match e with BigE => N.lor (getmem w e j m (a+i)) (N.shiftl (getmem w e i m a) (j*8))
               | LittleE => N.lor (getmem w e i m a) (N.shiftl (getmem w e j m (a+i)) (i*8))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_l, getmem_0, N.shiftl_0_l, N.shiftl_0_r, N.lor_0_r, N.lor_0_l. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, getmem_succ, N.add_succ_l. destruct e.
      rewrite N.shiftl_lor, N.shiftl_shiftl, N.lor_assoc, <- IHi, <- N.mul_add_distr_r. apply getmem_succ.
      rewrite (N.mul_succ_l i), <- N.shiftl_shiftl, <- N.lor_assoc, <- N.shiftl_lor, <- IHi. apply getmem_succ.
Qed.

Theorem setmem_split:
  forall w e i j m a v, setmem w e (i+j) m a v =
    match e with BigE => setmem w e j (setmem w e i m a (N.shiftr v (j*8))) (a+i) v
               | LittleE => setmem w e j (setmem w e i m a (v mod 2^(i*8))) (a+i) (N.shiftr v (i*8))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_r, N.shiftr_0_r, !setmem_0. destruct e; reflexivity.
    rewrite N.add_succ_comm. rewrite IHi. rewrite !(setmem_succ _ _ j). destruct e.

      erewrite <- setmem_1, <- N.add_1_r, N.mul_add_distr_r, <- N.shiftr_shiftr, <- IHi.
      rewrite N.add_1_r, N.add_succ_r. apply setmem_mod_r.

      erewrite <- setmem_1, <- IHi, N.add_succ_r, N.add_1_r, setmem_mod_r.
      rewrite N.shiftr_shiftr, N.mul_succ_l. reflexivity.
Qed.

Theorem getmem_mod:
  forall w e n2 n1 m a,
    (getmem w e n1 m a) mod 2^(n2*8) = getmem w e (N.min n1 n2) m
      match e with BigE => a + (n1 - n2) | LittleE => a end.
Proof.
  intros. destruct (N.le_ge_cases n1 n2).

    rewrite N.min_l, (proj2 (N.sub_0_le _ _) H), N.add_0_r by assumption.
    replace (match e with BigE => _ | _ => _ end) with a by (destruct e; reflexivity).
    apply N.mod_small. eapply N.lt_le_trans.
      apply getmem_bound.
      apply N.pow_le_mono_r. discriminate 1. apply N.mul_le_mono_r. assumption.

    rewrite N.min_r, <- N.land_ones by assumption. destruct e;
      [ rewrite <- (N.sub_add _ _ H) at 1
      | rewrite <- (N.add_sub n1 n2), N.add_comm, <- N.add_sub_assoc by assumption ];
      rewrite getmem_split, N.land_lor_distr_l, 2!N.land_ones, N.shiftl_mul_pow2;
      rewrite mp2_mod_mul, N.lor_0_r;
      apply N.mod_small, getmem_bound.
Qed.

Theorem shiftr_getmem:
  forall w e n2 n1 m a,
  N.shiftr (getmem w e n1 m a) (n2*8) = getmem w e (n1-n2) m
    match e with BigE => a | LittleE => a + n2 end.
Proof.
  intros. destruct (N.le_ge_cases n1 n2).

    rewrite (proj2 (N.sub_0_le _ _)), getmem_0 by assumption. eapply shiftr_low_pow2, N.lt_le_trans.
      apply getmem_bound.
      apply N.pow_le_mono_r. discriminate 1. apply N.mul_le_mono_r. assumption.

    destruct e;
    [ rewrite <- (N.sub_add _ _ H) at 1
    | rewrite <- (N.add_sub n1 n2), N.add_comm, <- N.add_sub_assoc at 1 by assumption ];
    rewrite getmem_split, N.shiftr_lor, N.shiftr_shiftl_r, N.sub_diag, N.shiftr_0_r by apply N.le_refl;
    rewrite shiftr_low_pow2 by apply getmem_bound; reflexivity.
Qed.

Theorem getbyte_spec:
  forall m a w i, N.testbit (getbyte m a w) i =
    andb (N.testbit m ((a mod 2^w)*8 + i)) (i <? 8).
Proof.
  intros. unfold getbyte. rewrite xbits_spec, N.add_comm, N.mul_succ_l.
  apply f_equal. destruct (_ <? _) eqn:H; symmetry.
    eapply N.ltb_lt, N.add_lt_mono_l, N.ltb_lt, H.
    eapply N.ltb_ge, N.add_le_mono_l, N.ltb_ge, H.
Qed.

Theorem setbyte_spec:
  forall m a v w i, N.testbit (setbyte m a v w) i =
    if andb ((a mod 2^w)*8 <=? i) (i <? N.succ(a mod 2^w)*8)
    then N.testbit v (i - (a mod 2^w)*8) else N.testbit m i.
Proof.
  intros. unfold setbyte. rewrite N.lor_spec, N.ldiff_spec, <- (N.land_ones v).
  destruct (_ <=? _) eqn:H1.

    rewrite !N.shiftl_spec_high', N.land_spec by apply N.leb_le, H1.
    destruct (_ <? _) eqn:H2.
      rewrite N.ones_spec_low.
        rewrite Bool.andb_false_r, Bool.andb_true_r. reflexivity.
        eapply N.add_lt_mono_r. rewrite N.sub_add.
          rewrite N.add_comm, <- N.mul_succ_l. apply N.ltb_lt, H2.
          apply N.leb_le, H1.
      rewrite N.ones_spec_high.
        rewrite Bool.andb_false_r, Bool.andb_true_r. apply Bool.orb_false_r.
        eapply N.add_le_mono_r. rewrite N.sub_add.
          rewrite N.add_comm, <- N.mul_succ_l. apply N.ltb_ge, H2.
          apply N.leb_le, H1.

    rewrite !N.shiftl_spec_low by apply N.leb_gt, H1.
    rewrite Bool.andb_true_r. apply Bool.orb_false_r.
Qed.

Theorem setbyte_frame:
  forall m a a' v w (NE: a' mod 2^w <> a mod 2^w),
  getbyte (setbyte m a v w) a' w = getbyte m a' w.
Proof.
  intros. apply N.bits_inj. intro i.
  rewrite !getbyte_spec, setbyte_spec.
  destruct (i <? 8) eqn:H1.

    apply N.ltb_lt in H1. apply N.lt_gt_cases in NE. destruct NE as [NE|NE].
      rewrite (proj2 (N.leb_gt _ _)).
        reflexivity.
        eapply N.lt_le_trans.
          apply N.add_lt_mono_l, H1.
          rewrite <- N.mul_succ_l. apply N.mul_le_mono_r, N.le_succ_l, NE.
      rewrite (proj2 (N.ltb_ge _ _)).
        rewrite Bool.andb_false_r. reflexivity.
        etransitivity.
          apply N.mul_le_mono_r, N.le_succ_l, NE.
          rewrite N.mul_comm. apply N.le_add_r.

    rewrite !Bool.andb_false_r. reflexivity.
Qed.

Theorem getbyte_setbyte:
  forall m a a' v w (EQ: a' mod 2^w = a mod 2^w),
  getbyte (setbyte m a v w) a' w = v mod 2^8.
Proof.
  intros. unfold getbyte, setbyte. rewrite EQ.
  rewrite xbits_lor, xbits_ldiff, !xbits_shiftl, xbits_ones.
  rewrite N.sub_diag, !N.shiftl_0_r, N.sub_0_r.
  rewrite <- N.mul_sub_distr_r, <- N.add_1_l, N.add_sub, N.mul_1_l.
  rewrite N.min_id, xbits_0_i, mp2_mod_mod.
  set (x := xbits _ _ _). destruct (N.eq_0_gt_0_cases x) as [H|H].
    rewrite H, N.ldiff_0_l. apply N.lor_0_l.
    rewrite N.ldiff_ones_r_low.
      apply N.lor_0_l.
      apply N.log2_lt_pow2. apply H.
        erewrite <- (N.mul_1_l 8), <- (N.add_sub 1), N.mul_sub_distr_r.
        apply xbits_bound.
Qed.

(* setmem doesn't modify addresses outside the interval [a, a+len). *)
Theorem setmem_frame:
  forall w e len m a v a' (LE: len <= msub w a' a),
  getbyte (setmem w e len m a v) a' w = getbyte m a' w.
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.

    assert (LE': len <= msub w a' (N.succ a)).
      apply N.succ_le_mono. rewrite <- !N.add_1_r, N.add_1_r.
      etransitivity; [|apply mp2_mod_le].
      rewrite <- add_msub_swap. rewrite madd_add_simpl_r_r. exact LE.
    rewrite setmem_succ. destruct e; rewrite IHlen by apply LE';
      apply setbyte_frame; intro H; revert LE;
        erewrite <- msub_mod_l, H, msub_mod_l, msub_diag by reflexivity;
        apply N.nle_succ_0.
Qed.

Theorem setmem_highbits:
  forall w e len m a v,
  N.shiftr (setmem w e len m a v) (2^w*8) = N.shiftr m (2^w*8).
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.
    rewrite setmem_succ. destruct e; rewrite IHlen; apply N.bits_inj; intro i;
     (rewrite !N.shiftr_spec', setbyte_spec, (proj2 (N.ltb_ge _ _));
      [ rewrite Bool.andb_false_r; reflexivity
      | etransitivity; [|apply N.le_add_l];
          apply N.mul_le_mono_r, N.le_succ_l, mp2_mod_lt ]).
Qed.

(* getmem doesn't read addresses outside the interval [a, a+len). *)
Theorem getmem_frame_mem:
  forall w e len m1 m2 a
    (FR: forall a', (msub w a' a < len) -> getbyte m1 a' w = getbyte m2 a' w),
  getmem w e len m1 a = getmem w e len m2 a.
Proof.
  intros. revert a FR. induction len using N.peano_ind; intros.
    reflexivity.
    rewrite !getmem_succ. rewrite !IHlen. rewrite FR. reflexivity.
      rewrite msub_diag. apply N.lt_0_succ.
      intros. apply FR. rewrite <- (madd_add_simpl_l_l w 1), <- add_msub_assoc, !N.add_1_l. eapply N.le_lt_trans.
        apply mp2_mod_le.
        apply -> N.succ_lt_mono. apply H.
Qed.

Theorem getmem_frame:
  forall w e1 e2 len1 len2 m a1 a2 v
    (LE1: len1 <= msub w a2 a1 \/ len2 = 0) (LE2: len2 <= msub w a1 a2 \/ len1 = 0),
  getmem w e1 len1 (setmem w e2 len2 m a2 v) a1 = getmem w e1 len1 m a1.
Proof.
  intros.
  destruct LE1 as [LE1|LE1]; [| rewrite LE1, setmem_0; reflexivity ].
  destruct LE2 as [LE2|LE2]; [| rewrite LE2, getmem_0; reflexivity ].
  apply getmem_frame_mem. intros. apply setmem_frame.
  etransitivity. exact LE2.
  etransitivity. apply N.le_add_r.
  erewrite <- (N.mod_small (_+_)), msub_mtele. reflexivity.
  eapply N.lt_le_trans. apply N.add_lt_mono_l, H.
  etransitivity. apply N.add_le_mono_l, LE1.
  rewrite msub_inv. reflexivity.
  intro H1. contradict H.
  erewrite <- msub_mod_l, <- msub_mod_r, H1, msub_diag in LE1 by reflexivity.
  apply N.le_0_r in LE1. rewrite LE1. apply N.nlt_0_r.
Qed.

Lemma recompose_bytes:
  forall w v, N.lor (v mod 2^w) (N.shiftl (N.shiftr v w) w) = v.
Proof.
  intros.
  rewrite <- N.ldiff_ones_r, <- N.land_ones, N.lor_comm.
  apply N.lor_ldiff_and.
Qed.

Lemma setmem_frame_byte:
  forall a' w en len m a n
    (LE: a' < 2^w -> len <= msub w a' a),
  xbits (setmem w en len m a n) (a' * 8) (N.succ a' * 8) =
  xbits m (a' * 8) (N.succ a' * 8).
Proof.
  intros. destruct (N.lt_ge_cases a' (2^w)).

    rewrite <- (N.mod_small _ _ H). apply setmem_frame. apply LE, H.

    rewrite <- (recompose_bytes (2^w*8) (setmem _ _ _ _ _ _)).
    rewrite setmem_highbits, !xbits_lor.
    rewrite xbits_above, N.lor_0_l.

      rewrite xbits_shiftl, <- !N.mul_sub_distr_r.
      rewrite (proj2 (N.sub_0_le _ _) H), N.mul_0_l, N.shiftl_0_r.
      rewrite xbits_shiftr, <- !N.mul_add_distr_r, !N.sub_add. reflexivity.
        etransitivity. apply H. apply N.le_succ_r. left. reflexivity.
        apply H.

      eapply N.lt_le_trans. apply mp2_mod_lt.
      apply N.pow_le_mono_r. discriminate.
      apply N.mul_le_mono_r, H.
Qed.

(* getmem inverts setmem *)
Theorem getmem_setmem:
  forall w e len m a v (LE: len <= 2^w),
  getmem w e len (setmem w e len m a v) a = v mod 2^(len*8).
Proof.
  intros until len. revert len w.
  induction len using N.peano_ind; intros.
    rewrite N.mul_0_l, N.mod_1_r. apply getmem_0.

    assert (LE': len <= msub w a (N.succ a)).
      rewrite <- N.add_1_r, msub_add_distr, msub_diag, msub_0_l by reflexivity.
      apply N.succ_le_mono. etransitivity. apply LE.
      destruct w as [|w]. reflexivity.
      rewrite (N.mod_small 1) by (apply N.pow_gt_1; [ reflexivity | discriminate 1 ]).
      rewrite N.mod_small.
        rewrite N.sub_1_r, mp2_succ_pred. reflexivity.
        apply N.sub_lt; [|reflexivity].
          change 1 with (N.succ 0). apply N.le_succ_l, mp2_gt_0.
    rewrite setmem_succ, getmem_succ. destruct e;
      rewrite IHlen by (etransitivity; [ apply N.le_succ_diag_r | exact LE ]);
      rewrite setmem_frame by apply LE';
      rewrite getbyte_setbyte by reflexivity.
        rewrite mp2_mod_mod, <- xbits_split_0, N.mul_succ_l. apply xbits_0_i.
        rewrite <- xbits_split_0, N.mul_succ_l, N.add_comm. apply xbits_0_i.
Qed.

Theorem setmem_byte_anylen:
  forall w en len i m a v (ILE: i < len),
  getbyte (setmem w en len m a v) (a+i) w = N.shiftr v (
    match en with BigE => msub w (N.pred len) i
                | LittleE => i + N.pred(len-i)/2^w*2^w end * 8) mod (2^8).
Proof.
  intros.
  set (r := N.succ (msub w (N.pred len) i)).
  assert (H: len = i + N.pred(len-i)/2^w*2^w + r). subst r.
    rewrite <- (N.sub_add i len) at 1 by apply N.lt_le_incl, ILE.
    rewrite <- (N.add_comm i), <- N.add_assoc. apply N.add_cancel_l.
    rewrite <- (N.succ_pred (len-i)) at 1 by apply N.sub_gt, ILE.
    rewrite (mp2_div_mod (N.pred(len - i)) w) at 1.
    rewrite N.mul_comm, <- N.add_succ_r.
    apply N.add_cancel_l. apply f_equal.
    rewrite <- N.sub_1_r, <- N.sub_add_distr, N.add_comm, N.sub_add_distr, N.sub_1_r.
    rewrite <- ofZ_toZ, msub_sbop, toZ_sub by apply N.lt_le_pred, ILE.
    erewrite ofZ_canonicalZ; reflexivity.
  assert (H': (len-r) mod 2^w = i mod 2^w).
    rewrite H. rewrite N.add_sub. apply mp2_mod_add.
  rewrite <- (N.sub_add r len) at 1 by (rewrite H, N.add_comm; apply N.le_add_r).
  rewrite <- (N.succ_pred r) at 2 by apply N.neq_succ_0.
  rewrite setmem_split, !setmem_succ, !setmem_mod_r.
  replace ((len-r) mod 2^w) with (i mod 2^w) by (symmetry;
    rewrite H, N.add_sub; apply mp2_mod_add).
  replace (N.pred r) with (msub w (N.pred len) i) by (symmetry; apply N.pred_succ).
  eenough (Hdef:_).
  destruct en.

  rewrite setmem_frame by exact Hdef.
  apply getbyte_setbyte.
  symmetry. rewrite <- mp2_add_r, H'. apply mp2_add_r.

  rewrite setmem_frame by exact Hdef.
  rewrite getbyte_setbyte. rewrite H at 1. rewrite N.add_sub. reflexivity.
  symmetry. rewrite <- mp2_add_r, H'. apply mp2_add_r.

  rewrite <- (msub_mod_r _ w (a+i)), <- N.add_1_r, <- mp2_add_l,
    <- (mp2_add_r _ (len-r)), H', mp2_add_r, mp2_add_l, msub_mod_r,
    msub_add_distr, msub_diag, msub_0_l by reflexivity.
  destruct w as [|w]. rewrite msub_0. apply N.le_0_l.
  rewrite (N.mod_small 1).
    rewrite N.mod_small.
      rewrite <- N.pred_sub. apply N.lt_le_pred, msub_lt.
      apply N_sub_lt. apply N.pow_nonzero. discriminate. discriminate.
    apply N.pow_gt_1. reflexivity. discriminate.
Qed.

Corollary setmem_byte:
  forall w en len i m a v (ILE: i < len) (LEN: len <= 2^w),
  getbyte (setmem w en len m a v) (a+i) w = N.shiftr v (
    match en with BigE => N.pred len - i | LittleE => i end * 8) mod (2^8).
Proof.
  intros. rewrite setmem_byte_anylen by assumption.
  assert (H: N.pred len < 2^w).
    apply N.succ_lt_mono, N.lt_succ_r. rewrite N.succ_pred. assumption.
    eapply N.neq_0_lt_0, N.lt_lt_0, ILE.
  destruct en.

    rewrite msub_nowrap;
    [ rewrite (N.mod_small (N.pred len)), (N.mod_small i) | rewrite !N.mod_small ];
    try first [ reflexivity | exact H | eapply N.lt_le_trans; eassumption ].
    apply N.lt_le_pred, ILE.

    rewrite N.div_small, N.mul_0_l, N.add_0_r. reflexivity.
    apply N.succ_lt_mono, N.lt_succ_r. rewrite N.succ_pred.
      etransitivity. apply N.le_sub_l. apply LEN.
      apply N.sub_gt, ILE.
Qed.

Theorem setmem_anybyte_anylen:
  forall a' w en len m a v,
    xbits (setmem w en len m a v) (a' * 8) (N.succ a' * 8) =
    if ((msub w a' a <? len) && (a' <? 2^w))%bool then
      N.shiftr v (
        match en with
        | BigE => msub w (a + N.pred len) a'
        | LittleE => msub w a' a + N.pred (len - msub w a' a) / 2^w * 2^w
        end * 8) mod 2^8
    else xbits m (a' * 8) (N.succ a' * 8).
Proof.
  intros. destruct andb eqn:H.

    apply andb_prop in H. destruct H as [H1 H2]. apply N.ltb_lt in H1, H2.
    rewrite <- (N.mod_small _ _ H2) at 1 2.
    rewrite <- add_msub_assoc, (N.add_comm a), <- msub_msub_distr.
    erewrite <- setmem_byte_anylen by eassumption.
    rewrite <- getbyte_mod_l, add_msub, getbyte_mod_l. reflexivity.

    apply Bool.andb_false_elim in H. destruct H as [H|H]; apply N.ltb_ge in H.
      apply setmem_frame_byte. intro. assumption.
      apply setmem_frame_byte. intro. contradict H. apply N.nle_gt. assumption.
Qed.

Theorem getmem_setmem_xbits:
  forall w en len i j m a v (LE: j + len <= 2^w),
  getmem w en len (setmem w en (i+len+j) m a v) (a+i) =
  match en with BigE => xbits v (j*8) ((j+len)*8) | LittleE => xbits v (i*8) ((i+len)*8) end.
Proof.
  intros.
  assert (H1: len <= len mod 2^w \/ j = 0). destruct j as [|j].
    right. reflexivity.
    left. rewrite N.mod_small. reflexivity. eapply N.add_lt_mono_l, N.le_lt_trans.
      apply LE.
      rewrite N.add_comm. apply N.lt_add_pos_r. reflexivity.
  assert (H2: j <= msub w 0 len \/ len = 0).
    destruct len as [|len]. right. reflexivity.
    destruct j as [|j]. left. apply N.le_0_l.
    left. assert (H2: N.pos len < 2^w).
      eapply N.lt_le_trans; [|exact LE]. apply N.lt_add_pos_l. reflexivity.
    eapply N.add_le_mono_r. rewrite msub_inv, msub_0_r, N.mod_small. assumption.
      assumption.
      rewrite mp2_mod_0_l, N.mod_small. discriminate 1. assumption.
  rewrite !setmem_split. destruct en; (rewrite getmem_frame;
  [ (rewrite getmem_setmem; [| etransitivity;
     [ apply N.le_add_r | rewrite N.add_comm; exact LE ] ])
  | rewrite madd_add_simpl_l_l, add_msub_l; assumption
  | rewrite madd_add_simpl_l_l, msub_add_distr, msub_diag; assumption ] ).

    unfold xbits. rewrite <- N.mul_sub_distr_r, N.add_comm, N.add_sub. reflexivity.

    rewrite N.add_comm, N.mul_add_distr_r, <- xbits_equiv. unfold xbits.
    rewrite N.add_sub, mp2_mod_mod. reflexivity.
Qed.

Theorem setmem_merge:
  forall w e i j m a v1 v2,
  setmem w e j (setmem w e i m a v1) (a+i) v2 =
  setmem w e (i+j) m a match e with
                       | BigE => cbits v1 (j*8) (v2 mod 2^(j*8))
                       | LittleE => cbits v2 (i*8) (v1 mod 2^(i*8))
                       end.
Proof.
  symmetry.
  assert (H:=setmem_split w e i j m a). destruct e;
  [ specialize (H (cbits v1 (j*8) (v2 mod 2^(j*8))))
  | specialize (H (cbits v2 (i*8) (v1 mod 2^(i*8)))) ];
  rewrite shiftr_cbits, <- (setmem_mod_r _ _ j), cbits_mod, !setmem_mod_r in H by apply mp2_mod_lt;
  apply H.
Qed.

Definition overlap w a1 len1 a2 len2 :=
  exists i j, i < len1 /\ j < len2 /\ (a1 + i) mod 2^w = (a2 + j) mod 2^w.

Theorem overlap_reflexivity:
  forall w a len1 len2, 0 < len1 -> 0 < len2 -> overlap w a len1 a len2.
Proof.
  intros. exists 0,0. repeat split; assumption.
Qed.

Theorem overlap_symmetry:
  forall w a1 len1 a2 len2, overlap w a1 len1 a2 len2 -> overlap w a2 len2 a1 len1.
Proof.
  unfold overlap. intros. destruct H as [i [j [H1 [H2 H3]]]].
  exists j,i. repeat split; [..|symmetry]; assumption.
Qed.

Corollary noverlap_symmetry:
  forall w a1 len1 a2 len2, ~overlap w a1 len1 a2 len2 -> ~overlap w a2 len2 a1 len1.
Proof.
  intros. intro H1. apply H, overlap_symmetry, H1.
Qed.

Theorem overlap_mod_l:
  forall w a1 len1 a2 len2,
  overlap w (a1 mod 2^w) len1 a2 len2 <-> overlap w a1 len1 a2 len2.
Proof.
  split; intro; destruct H as [i [j [H1 [H2 H3]]]]; exists i,j; repeat split; try assumption.
    rewrite <- mp2_add_l. assumption.
    rewrite mp2_add_l. assumption.
Qed.

Corollary overlap_mod_r:
  forall w a1 len1 a2 len2,
  overlap w a1 len1 (a2 mod 2^w) len2 <-> overlap w a1 len1 a2 len2.
Proof.
  split; intro; apply overlap_symmetry, overlap_mod_l, overlap_symmetry, H.
Qed.

Theorem overlap_0_l:
  forall w a1 a2 len2, ~overlap w a1 0 a2 len2.
Proof.
  intros. intro H. destruct H as [i [j [H1 [H2 H3]]]]. eapply N.nlt_0_r, H1.
Qed.

Theorem overlap_0_r:
  forall w a1 len1 a2, ~overlap w a1 len1 a2 0.
Proof.
  intros. intro H. eapply overlap_0_l, overlap_symmetry, H.
Qed.

Theorem noverlap:
  forall w a1 len1 a2 len2,
    ~overlap w a1 len1 a2 len2 <->
    (forall i j, i < len1 -> j < len2 -> (a1 + i) mod 2^w <> (a2 + j) mod 2^w).
Proof.
  split; intros; intro.
    apply H. exists i,j. repeat split; assumption.
    destruct H0 as [i [j [H1 [H2 H3]]]]. eapply H; eassumption.
Qed.

Theorem overlap1_noverlap_trans:
  forall w a a1 len1 a2 len2
    (OV: overlap w a 1 a1 len1) (NO: ~overlap w a1 len1 a2 len2),
  ~overlap w a 1 a2 len2.
Proof.
  intros. destruct OV as [i [j [I1 [J1 H]]]].
  apply noverlap. intros i' j' I'1 J2.
  apply N.lt_1_r in I1,I'1. subst i i'. rewrite N.add_0_r in *.
  intro H'. apply NO. exists j,j'. repeat split; try assumption.
  rewrite <- H. apply H'.
Qed.

Theorem overlap_grow:
  forall w a1 len1 a2 len2 a1' len1',
    msub w a1 a1' + len1 <= len1' ->
  overlap w a1 len1 a2 len2 -> overlap w a1' len1' a2 len2.
Proof.
  intros. destruct H0 as [i [j [H1 [H2 H3]]]].
  exists (msub w a1 a1' + i),j. repeat split.
    eapply N.lt_le_trans. apply N.add_lt_mono_l, H1. exact H.
    assumption.
    rewrite N.add_assoc, <- mp2_add_l, add_msub_assoc, add_msub_l, mp2_add_l. exact H3.
Qed.

Corollary noverlap_shrink:
  forall w a1 len1 a2 len2 a1' len1',
    msub w a1' a1 + len1' <= len1 ->
  ~overlap w a1 len1 a2 len2 -> ~overlap w a1' len1' a2 len2.
Proof.
  intros. intro H1. apply H0. revert H1. apply overlap_grow. assumption.
Qed.

Theorem overlap_shiftr:
  forall w a1 len1 a2 len2 i,
  overlap w (a1+i) len1 (a2+i) len2 <-> overlap w a1 len1 a2 len2.
Proof.
  split; intro H; destruct H as [i1 [j1 [H1 [H2 H3]]]];
  exists i1,j1; repeat split; try assumption.

    rewrite !(N.add_comm _ i), <- !N.add_assoc in H3.
    apply (f_equal (fun x => msub w x i)) in H3.
    rewrite !msub_mod_l, !add_msub_l in H3 by reflexivity.
    assumption.

    rewrite (N.add_comm a1), (N.add_comm a2), <- !N.add_assoc.
    rewrite <- !(mp2_add_r _ (_+_)), H3. reflexivity.
Qed.

Corollary noverlap_shiftr:
  forall w a1 len1 a2 len2 i,
  ~overlap w (a1+i) len1 (a2+i) len2 <-> ~overlap w a1 len1 a2 len2.
Proof.
  split; intros H H1; apply H.
    apply overlap_shiftr, H1.
    apply -> overlap_shiftr. apply H1.
Qed.

Theorem overlap_shiftl:
  forall w a1 len1 a2 len2 i,
  overlap w (msub w a1 i) len1 (msub w a2 i) len2 <->
  overlap w a1 len1 a2 len2.
Proof.
  split; intro H; destruct H as [i1 [j1 [H1 [H2 H3]]]];
  exists i1,j1; repeat split; try assumption.

  rewrite <- !add_msub_swap in H3.
  apply (f_equal (fun x => (x+i) mod 2^w)) in H3.
  rewrite !msub_add in H3.
  assumption.

  rewrite <- !add_msub_swap, <- !(msub_mod_l w w (_+_)), H3; reflexivity.
Qed.

Corollary noverlap_shiftl:
  forall w a1 len1 a2 len2 i,
  ~overlap w (msub w a1 i) len1 (msub w a2 i) len2 <->
  ~overlap w a1 len1 a2 len2.
Proof.
  split; intros H H1; apply H.
    apply overlap_shiftl, H1.
    apply -> overlap_shiftl. apply H1.
Qed.

Theorem overlap_rev:
  forall w a1 len1 a2 len2 i,
  overlap w (msub w i (a1+len1)) len1 (msub w i (a2+len2)) len2 <->
  overlap w a1 len1 a2 len2.
Proof.
  assert (H: forall w a1 len1 a2 len2 i, overlap w a1 len1 a2 len2 ->
             overlap w (msub w i (a1+len1)) len1 (msub w i (a2+len2)) len2).
   intros. destruct H as [i1 [j1 [H1 [H2 H3]]]].
   exists (len1-N.succ i1), (len2-N.succ j1). repeat split.
    apply N_sub_lt.
      eapply N.neq_0_lt_0, N.le_lt_trans. apply N.le_0_l. apply H1.
      apply N.neq_succ_0.
    apply N_sub_lt.
      eapply N.neq_0_lt_0, N.le_lt_trans. apply N.le_0_l. apply H2.
      apply N.neq_succ_0.
    rewrite <- !add_msub_swap, !msub_sbop, !toZ_add, !canonicalZ_sub.
    rewrite !toZ_sub by (apply N.le_succ_l; assumption).
    rewrite !(Z.add_comm _ (canonicalZ _ _)), <- !Z.add_sub_assoc, !canonicalZ_add_l.
    rewrite <- !Z.add_sub_swap, !Z.sub_add_distr, !Zplus_minus, <- !Z.sub_add_distr.
    rewrite <- !(canonicalZ_sub_r _ _ (_+_)), <- !toZ_add, <- !N.add_1_r, !N.add_assoc.
    rewrite<- (toZ_mod_pow2 w w (_+1)), <- mp2_add_l, H3, mp2_add_l, toZ_mod_pow2;
    reflexivity.

  split; [|apply H]. intro H1.
  apply H with (i:=0) in H1.
  rewrite <- !(msub_mod_r w w 0 (_+_)), <- !add_msub_swap, !madd_add_simpl_r_r in H1 by reflexivity.
  rewrite !msub_msub_distr, <- !add_msub_swap, !N.add_0_l in H1.
  revert H1. apply overlap_shiftl.
Qed.

Corollary noverlap_rev:
  forall w a1 len1 a2 len2 i,
  ~overlap w (msub w i (a1+len1)) len1 (msub w i (a2+len2)) len2 <->
  ~overlap w a1 len1 a2 len2.
Proof.
  split; intros H H1; apply H.
    apply overlap_rev, H1.
    apply -> overlap_rev. apply H1.
Qed.

Theorem sep_noverlap:
  forall w a1 len1 a2 len2
    (LE1: len1 <= msub w a2 a1 \/ len2 = 0) (LE2: len2 <= msub w a1 a2 \/ len1 = 0),
  ~overlap w a1 len1 a2 len2.
Proof.
  intros.
  destruct LE1 as [LE1|H]; [|subst len2; apply overlap_0_r].
  destruct LE2 as [LE2|H]; [|subst len1; apply overlap_0_l].
  intro H. revert LE2. apply N.nle_gt.
  destruct H as [i [j [H1 [H2 H3]]]].
  destruct (N.le_gt_cases (2^w) len2) as [H4|H4].
    eapply N.lt_le_trans. apply msub_lt. exact H4.
  eapply N.le_lt_trans; [|exact H2].
  rewrite <- (N.mod_small j (2^w)) by (etransitivity; eassumption).
  rewrite <- (add_msub_l w a2 j).
  rewrite <- (msub_mod_l w w (a2+j)) by reflexivity.
  rewrite <- H3.
  rewrite msub_mod_l by reflexivity.
  rewrite add_msub_swap. rewrite N.mod_small. apply N.le_add_r.
  eapply N.lt_le_trans. apply N.add_lt_mono_l. exact H1.
  etransitivity. apply N.add_le_mono_l. exact LE1.
  destruct (N.eq_dec (a1 mod 2^w) (a2 mod 2^w)).
    rewrite <- (msub_mod_l w w a1), <- (msub_mod_r w w _ a1), e, msub_mod_l, msub_mod_r,
            msub_diag by reflexivity. apply N.le_0_l.
    rewrite msub_inv by assumption. reflexivity.
Qed.

Theorem noverlap_sep:
  forall w a1 len1 a2 len2
    (NO: ~overlap w a1 len1 a2 len2),
  len2 <= msub w a1 a2 \/ len1 = 0.
Proof.
  intros.
  destruct len1 as [|len1]. right. reflexivity. left.
  intro H. apply N.compare_gt_iff in H. apply NO.
  exists 0,(msub w a1 a2). repeat split.
    assumption.
    rewrite add_msub, N.add_0_r. reflexivity.
Qed.

Theorem noverlap_sum:
  forall w a1 len1 a2 len2
    (SZ: len1 + msub w a2 (a1+len1) + len2 <= 2^w),
  ~overlap w a1 len1 a2 len2.
Proof.
  intros.
  destruct len2 as [|len2]. apply overlap_0_r.
  assert (GAP: len1 + msub w a2 (a1+len1) < 2^w).
    eapply (N.le_lt_trans _ (_+0)). apply N.le_add_r. eapply N.lt_le_trans; [|exact SZ].
    apply N.add_lt_mono_l. reflexivity.
  assert (LEN1: len1 < 2^w).
    eapply N.le_lt_trans. apply N.le_add_r. exact GAP.
  apply sep_noverlap.

  left. apply N.le_ngt. intro H. revert SZ. apply N.nle_gt.
  rewrite msub_add_distr, msub_wrap by
    (rewrite msub_mod_pow2, N.min_id, (N.mod_small _ _ LEN1); apply H).
  rewrite msub_mod_pow2, N.min_id, N.mod_small, (N.add_comm len1) by assumption.
  rewrite N.sub_add by (etransitivity; [ apply N.lt_le_incl, LEN1 | apply N.le_add_r ]).
  rewrite <- N.add_assoc. apply N.lt_add_pos_r. destruct msub in |- *; reflexivity.

  rewrite msub_add_distr in GAP.
  destruct (N.eq_dec (a1 mod 2^w) (a2 mod 2^w)). right.
    rewrite <- (msub_mod_r w w a2), e, msub_mod_r, msub_diag in GAP by reflexivity.
    rewrite <- (N.mod_small _ _ LEN1), <- (msub_0_r w len1) in GAP at 1.
    destruct len1. reflexivity. contradict GAP. rewrite msub_inv. apply N.lt_irrefl.
    rewrite (N.mod_small _ _ LEN1), mp2_mod_0_l.
    discriminate 1.
  left. eapply N.add_le_mono_r. rewrite (msub_inv _ _ _ n), N.add_comm.
  etransitivity; [|apply SZ]. apply N.add_le_mono_r.
  etransitivity; [|apply N.Div0.mod_le].
  rewrite msub_add_distr, add_msub, msub_mod_pow2, N.min_id. reflexivity.
Qed.

Theorem overlap_start:
  forall w a1 len1 a2 len2
    (OL: overlap w a1 len1 a2 len2),
  msub w a1 a2 < len2 \/ msub w a2 a1 < len1.
Proof.
  intros.
  destruct (N.lt_ge_cases (msub w a1 a2) len2). left. exact H. right.
  apply N.nle_gt. intro H1. revert OL. apply sep_noverlap; left; assumption.
Qed.

Theorem overlap_dec:
  forall w a1 len1 a2 len2, {overlap w a1 len1 a2 len2}+{~overlap w a1 len1 a2 len2}.
Proof.
  intros.
  pose (f := fix f len := match len with O => false | S m => orb (msub w (a2 + N.of_nat m) a1 <? len1) (f m) end).
  enough (H: f (N.to_nat len2) = true <-> overlap w a1 len1 a2 len2).
  destruct (f (N.to_nat len2)).
    left. apply H. reflexivity.
    right. intro H0. apply H in H0. discriminate.
  rewrite <- (N2Nat.id len2) at 2. generalize (N.to_nat len2). clear len2. intro len2.
  split; intro; induction len2.
    discriminate.
    simpl in H. apply Bool.orb_prop in H. destruct H.
      exists (msub w (a2 + N.of_nat len2) a1), (N.of_nat len2). repeat split.
        apply N.ltb_lt, H.
        rewrite Nat2N.inj_succ. apply N.lt_succ_diag_r.
        rewrite add_msub. reflexivity.
      eapply IHlen2 in H. destruct H as [i [j [H1 [H2 H3]]]]. exists i,j. repeat split; try assumption.
        etransitivity. eassumption. rewrite Nat2N.inj_succ. apply N.lt_succ_diag_r.
    contradict H. apply overlap_0_r.
    destruct H as [i [j [H1 [H2 H3]]]]. rewrite Nat2N.inj_succ in H2. apply N.lt_succ_r, N.le_lteq in H2. destruct H2.
      simpl. rewrite IHlen2.
        apply Bool.orb_true_r.
        exists i,j. repeat split; assumption.
      simpl. rewrite (proj2 (N.ltb_lt _ len1)). reflexivity.
        erewrite <- H, <- msub_mod_l, <- H3, msub_mod_l, add_msub_l by reflexivity. eapply N.le_lt_trans.
          apply mp2_mod_le.
          assumption.
Qed.

Theorem overlap_getbyte_updated:
  forall w en a1 a2 len v (OV: overlap w a1 1 a2 len) m1 m2,
  getbyte (setmem w en len m1 a2 v) a1 w = getbyte (setmem w en len m2 a2 v) a1 w.
Proof.
  intros. destruct OV as [i [j [I1 [J1 H]]]].
  apply N.lt_1_r in I1. subst i. rewrite N.add_0_r in H.
  rewrite <- !(getbyte_mod_l _ a1), H, !getbyte_mod_l.
  rewrite !setmem_byte_anylen by assumption. reflexivity.
Qed.

Theorem update_frame_noverlap:
  forall mem w a1 len1 a2 len2 (v:N)
    (NO: ~overlap w a1 len1 a2 len2) (LT1: 0 < len1) (LT2: 0 < len2),
  getbyte (setbyte mem a1 v w) a2 w = getbyte mem a2 w.
Proof.
  intros. apply setbyte_frame. intro H. apply NO. symmetry in H.
  exists 0,0. repeat split; rewrite ?N.add_0_r; assumption.
Qed.

Theorem update_frame_noverlap_index:
  forall mem w a1 len1 a2 len2 i j (v:N)
    (NO: ~overlap w a1 len1 a2 len2) (LT1: i < len1) (LT2: j < len2),
  getbyte (setbyte mem (a1+i) v w) (a2+j) w = getbyte mem (a2+j) w.
Proof.
  intros. apply setbyte_frame. intro H. apply NO. symmetry in H.
  exists i,j. repeat split; assumption.
Qed.

Theorem getmem_noverlap:
  forall w e1 e2 len1 len2 m a1 a2 v
    (NO: ~overlap w a1 len1 a2 len2),
  getmem w e1 len1 (setmem w e2 len2 m a2 v) a1 = getmem w e1 len1 m a1.
Proof.
  intros.
  assert (NO2 := noverlap_symmetry _ _ _ _ _ NO).
  apply noverlap_sep in NO,NO2.
  apply getmem_frame; assumption.
Qed.

Theorem getmem_frame_noverlap_index:
  forall w e1 e2 mem a1 blen1 a2 blen2 i j len1 len2 v
    (NO: ~overlap w a1 blen1 a2 blen2) (LE1: i + len1 <= blen1) (LE2: j + len2 <= blen2),
  getmem w e2 len2 (setmem w e1 len1 mem (a1+i) v) (a2+j) = getmem w e2 len2 mem (a2+j).
Proof.
  intros. apply getmem_noverlap. eapply noverlap_shrink.
    rewrite add_msub_l. etransitivity; [|exact LE2].
      apply N.add_le_mono_r, mp2_mod_le.
    apply noverlap_symmetry. eapply noverlap_shrink.
      rewrite add_msub_l. etransitivity; [|exact LE1].
        apply N.add_le_mono_r, mp2_mod_le.
      exact NO.
Qed.

Theorem getbyte_mod_mem:
  forall m a w, getbyte (m mod (memsize w)) a w = getbyte m a w.
Proof.
  intros. unfold getbyte, memsize.
  rewrite xbits_equiv, mp2_mod_mod_min, N.min_r, <- xbits_equiv. reflexivity.
  apply N.mul_le_mono_r, N.le_succ_l, mp2_mod_lt.
Qed.

Theorem byte_equivalent:
  forall w m1 m2 (EQ: forall a, getbyte m1 a w = getbyte m2 a w),
  m1 mod (memsize w) = m2 mod (memsize w).
Proof.
  intros.
  apply N.bits_inj. intro i. destruct (N.lt_ge_cases i (2^w*8)) as [H|H].

    rewrite <- (Bool.andb_true_r (N.testbit (m1 mod _) _)), <- (Bool.andb_true_r (N.testbit (m2 mod _) _)).
    replace true with (i <? N.succ ((i/8) mod 2^w) * 8).
    rewrite (N.div_mod' i 8), N.add_comm.
    rewrite <- !xbits_spec.
    rewrite N.add_comm, <- N.div_mod', (N.mul_comm 8).
    rewrite <- (N.mod_small (i/8) (2^w)) by (apply N.Div0.div_lt_upper_bound; rewrite N.mul_comm; apply H).
    rewrite mp2_mod_mod.
    change (xbits (m1 mod _) _ _) with (getbyte (m1 mod memsize w) (i/8) w).
    rewrite getbyte_mod_mem, EQ, <- getbyte_mod_mem. reflexivity.

      apply N.ltb_lt. rewrite N.mod_small by (apply N.Div0.div_lt_upper_bound; rewrite N.mul_comm; apply H).
      rewrite (N.div_mod' i 8) at 1. rewrite N.mul_succ_l, (N.mul_comm 8).
      apply N.add_lt_mono_l, N.mod_lt. discriminate.

    unfold memsize. rewrite !N.mod_pow2_bits_high by apply H. reflexivity.
Qed.

Theorem bytes_inj:
  forall m1 m2
    (EQ: forall a, xbits m1 (a*8) (N.succ a * 8) = xbits m2 (a*8) (N.succ a * 8)),
  m1 = m2.
Proof.
  intros. apply N.bits_inj. intro i.
  rewrite (N.div_mod' i 8), N.mul_comm, N.add_comm, <- !N.shiftr_spec'.
  rewrite <- 2!(N.mod_pow2_bits_low (N.shiftr _ _) 8) by apply (mp2_mod_lt _ 3).
  specialize (EQ (i/8)). unfold xbits in EQ.
  rewrite N.mul_succ_l, (N.add_comm _ 8), N.add_sub in EQ.
  rewrite EQ. reflexivity.
Qed.

Theorem setmem_swap:
  forall w e len1 len2 m a1 a2 v1 v2
    (NO: ~overlap w a1 len1 a2 len2),
  setmem w e len2 (setmem w e len1 m a1 v1) a2 v2 =
  setmem w e len1 (setmem w e len2 m a2 v2) a1 v1.
Proof.
  intros.
  rewrite <- (recompose_bytes (2^w*8) (setmem w e _ _ _ _)). symmetry.
  rewrite <- (recompose_bytes (2^w*8) (setmem w e _ _ _ _)).
  rewrite !setmem_highbits. apply f_equal2; [|reflexivity].
  apply byte_equivalent. intro a.
  destruct (overlap_dec w a 1 a1 len1) as [H1|H1].

    erewrite overlap_getbyte_updated by assumption.
    symmetry. rewrite <- (getmem_1 w e), getmem_noverlap.
      rewrite getmem_1. reflexivity.
      eapply overlap1_noverlap_trans; eassumption.

    rewrite <- (getmem_1 w e), getmem_noverlap by assumption.
    destruct (overlap_dec w a 1 a2 len2) as [H2|H2].
      rewrite getmem_1. symmetry. apply overlap_getbyte_updated, H2.
      rewrite <- (getmem_1 w e), !getmem_noverlap by assumption. reflexivity.
Qed.

Theorem setmem_merge_rev:
  forall w e i j m a v1 v2, i + j < 2^w ->
  setmem w e j (setmem w e i m a v2) (msub w a j) v1 =
  setmem w e (i+j) m (msub w a j) match e with
                                  | BigE => cbits v1 (i*8) (v2 mod 2^(i*8))
                                  | LittleE => cbits v2 (j*8) (v1 mod 2^(j*8))
                                  end.
Proof.
  intros.
  rewrite setmem_swap.
    rewrite N.add_comm, <- setmem_mod_l, <- (msub_add _ _ j), setmem_mod_l. apply setmem_merge.

    apply noverlap_sum.
    rewrite (N.add_comm i), <- N.add_assoc, msub_comm, <- (N.add_0_r a),
            madd_add_simpl_l_l, <- msub_add_distr at 1.
    destruct (N.eq_dec (i+j) 0) as [H'|H'].
      rewrite H', msub_diag. apply N.le_0_l.
      rewrite N.add_comm, <- (N.mod_small _ _ H), <- (msub_0_r w (i+j)), msub_inv at 1.
        reflexivity.
        rewrite (N.mod_small _ _ H). exact H'.
Qed.

End MemTheory.



Module Type PICINAE_THEORY (IL: PICINAE_IL).

Import IL.
Open Scope N.

(* Define an alternative inductive principle for structural inductions on stmts
   that works better for proving properties of *executed* stmts that might contain
   repeat-loops.  The cases for all non-repeat forms are the same as Coq's default
   stmt_ind principle, but properties P of repeat-loops are provable from assuming
   that the expansion of the loop into a sequence satisfies P.
 *)
Theorem stmt_ind2 (P: stmt -> Prop):
  P Nop ->
  (forall v e, P (Move v e)) ->
  (forall e, P (Jmp e)) ->
  (forall i, P (Exn i)) ->
  (forall q1 q2 (IHq1: P q1) (IHq2: P q2), P (Seq q1 q2)) ->
  (forall e q1 q2 (IHq1: P q1) (IHq2: P q2), P (If e q1 q2)) ->
  (forall e q (IHq1: P q) (IHq2: forall n, P (N.iter n (Seq q) Nop)), P (Rep e q)) ->
  forall (q:stmt), P q.
Proof.
  intros. induction q.
    assumption.
    apply H0.
    apply H1.
    apply H2.
    apply H3; assumption.
    apply H4; assumption.
    apply H5. assumption. apply Niter_invariant.
      apply H.
      intros. apply H3; assumption.
Qed.

Section XPPartitions.

Definition can_step_between p (t1 t2:trace) :=
  match t1, ostartof t2 with xs1::_, Some xs2 => can_step p (xs2,xs1) | _,_ => True end.

Theorem exec_prog_nil:
  forall p, exec_prog p nil.
Proof. intro. apply Forall_nil. Qed.

Theorem exec_prog_none:
  forall p xs, exec_prog p (xs::nil).
Proof. intros. apply Forall_nil. Qed.

(* Add a next step to a trace. *)
Theorem exec_prog_step:
  forall p t xs' (XP: exec_prog p t)
    (CS: match t with nil => True | xs::_ => can_step p (xs',xs) end),
  exec_prog p (xs'::t).
Proof.
  intros. destruct t as [|xs t].
    apply Forall_nil.
    unfold exec_prog. rewrite stepsof_cons. apply Forall_cons; assumption.
Qed.

(* Delete the final step from a trace. *)
Theorem exec_prog_tail:
  forall p t xs' (XP: exec_prog p (xs'::t)),
  exec_prog p t.
Proof.
  unfold exec_prog. intros. destruct t as [|xs t].
    apply Forall_nil.
    eapply Forall_inv_tail, XP.
Qed.

(* Extract the final step of a trace. *)
Theorem exec_prog_final:
  forall p t xs' xs (XP: exec_prog p (xs'::xs::t)),
  can_step p (xs',xs).
Proof.
  intros. eapply Forall_inv, XP.
Qed.

(* Concatenate two exec_prog comptations into one whole. *)
Theorem exec_prog_app:
  forall p t1 t2
    (XP1: exec_prog p t1) (CS: can_step_between p t1 t2) (XP2: exec_prog p t2),
  exec_prog p (t2++t1).
Proof.
  intros. destruct t1 as [|xs1 t1].
    rewrite app_nil_r. exact XP2.
    unfold exec_prog. rewrite stepsof_app. apply Forall_app. split.
      exact XP2.
      apply Forall_app. split; [|apply XP1]. unfold can_step_between in CS. destruct ostartof as [xs2|].
        apply Forall_cons. exact CS. apply Forall_nil.
        apply Forall_nil.
Qed.

(* Prepend a step to an exec_prog computation. *)
Corollary exec_prog_prepend:
  forall xs0 p t (XP: exec_prog p t)
    (CS: match ostartof t with None => True | Some xs1 => can_step p (xs1,xs0) end),
    exec_prog p (t++xs0::nil).
Proof.
  intros. apply exec_prog_app.
    apply Forall_nil.
    unfold can_step_between. destruct ostartof as [xs1|].
      exact CS.
      exact I.
    exact XP.
Qed.

(* Split an exec_prog computation into two parts. *)
Theorem exec_prog_split:
  forall p t1 t2 (XP: exec_prog p (t2++t1)),
  exec_prog p t1 /\ can_step_between p t1 t2 /\ exec_prog p t2.
Proof.
  intros. unfold exec_prog in XP. rewrite stepsof_app in XP.
  apply Forall_app in XP. destruct XP as [XP2 XP].
  apply Forall_app in XP. destruct XP as [CS XP1].
  split. exact XP1. split; [|exact XP2].
  unfold can_step_between. destruct t1 as [|xs1].
    exact I.
    destruct ostartof as [xs2|].
      eapply Forall_inv. exact CS.
      exact I.
Qed.

(* Delete the first step from a trace. *)
Corollary exec_prog_suffix:
  forall p xs t (XP: exec_prog p (t++xs::nil)),
  exec_prog p t.
Proof.
  intros. apply exec_prog_split in XP. apply XP.
Qed.

End XPPartitions.



Section Determinism.

(* The semantics of eval_exp, exec_stmt, and exec_prog are deterministic
   as long as there are no Unknown expressions. *)

Theorem eval_exp_deterministic:
  forall {e c s n1 t1 n2 t2} (NU: forall_exps_in_exp not_unknown e)
         (E1: eval_exp c s e n1 t1) (E2: eval_exp c s e n2 t2), (n1,t1)=(n2,t2).
Proof.
  induction e; intros; inversion E1; inversion E2; clear E1 E2; subst;
  simpl in NU; repeat match type of NU with _ /\ _ => let H := fresh NU in destruct NU as [H NU] end;
  try (remember (match n0 with N0 => e3 | _ => e2 end) as e);
  repeat match goal with [ IH: forall _ _ _ _ _ _, _ -> eval_exp _ _ ?e _ _ -> eval_exp _ _ ?e _ _ -> _=_,
                           H0: exps_in_exp and not_unknown ?e,
                           H1: eval_exp ?c ?s ?e ?n1 ?t1,
                           H2: eval_exp ?c ?s ?e ?n2 ?t2 |- _ ] =>
           specialize (IH c s n1 t1 n2 t2 H0 H1 H2); clear H0 H1 H2;
           try (injection IH; clear IH; intros); subst;
           try match type of E' with
             eval_exp _ _ (match ?N with N0 => _ | _ => _ end) _ _ => destruct N
           end
         end;
  try reflexivity.

  rewrite TYP0 in TYP. inversion TYP. reflexivity.
  exfalso. assumption.
Qed.

Theorem exec_stmt_deterministic:
  forall {c s q c1 s1 x1 c2 s2 x2} (NU: forall_exps_in_stmt not_unknown q)
         (X1: exec_stmt c s q c1 s1 x1) (X2: exec_stmt c s q c2 s2 x2),
  (x1,c1,s1) = (x2,c2,s2).
Proof.
  intros. revert c2 s2 x2 X2.
  dependent induction X1; intros; inversion X2; subst;
  try solve [ split;reflexivity ];
  try destruct NU as [NU1 NU2].

  assert (H:=eval_exp_deterministic NU E E0). inversion H. reflexivity.

  assert (H:=eval_exp_deterministic NU E E0).
  inversion H. subst. reflexivity.

  apply IHX1; assumption.

  apply (IHX1 NU1) in XS1. discriminate.

  apply (IHX1_1 NU1) in XS. discriminate.

  apply (IHX1_1 NU1) in XS1. inversion XS1. subst. apply (IHX1_2 NU2) in XS0. assumption.

  apply IHX1.
    destruct NU2. destruct b; assumption.
    assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst. assumption.

  assert (H:=eval_exp_deterministic NU1 E E0). inversion H; subst.
  apply IHX1.
    apply Niter_invariant. exact I. split; assumption.
    assumption.
Qed.

Theorem exec_prog_deterministic:
  forall {p t1 t2 xs} (NU: forall_exps_in_prog not_unknown p)
  (XP1: exec_prog p (t1++xs::nil)) (XP2: exec_prog p (t2++xs::nil)),
  exists t, t1 = t++t2 \/ t2 = t++t1.
Proof.
  intros. induction t1; intros.
    exists t2. right. symmetry. apply app_nil_r.
    destruct IHt1 as [t [IH|IH]].
      eapply exec_prog_tail, XP1.
      subst. exists (a::t). left. reflexivity.
      subst. rewrite <- (rev_involutive t) in *. destruct (rev t) as [|b t'].
        exists (a::nil). left. reflexivity.
        replace b with a.
          exists (rev t'). right. rewrite rev_cons, <- app_assoc. reflexivity.

  rewrite rev_cons in XP2. rewrite <- app_assoc in XP2. simpl in XP1.
  destruct (t1++xs::nil) as [|(x,s) t1'] eqn:H.
    apply app_eq_nil,proj2 in H. discriminate H.
  apply exec_prog_final in XP1.
  apply exec_prog_split,proj2,proj1 in XP2. simpl in XP2. rewrite ostartof_niltail in XP2.
  inversion XP1; subst. inversion XP2; subst.
  rewrite LU0 in LU. inversion LU; subst.
  eapply exec_stmt_deterministic in XS. inversion XS; subst. reflexivity.
    apply (NU _ _ _ _ LU0).
    exact XS0.
Qed.

End Determinism.


Section Monotonicity.

(* exec_prog is monotonic with respect to programs.  Enlarging the space of known
   instructions in memory preserves executions. *)

Theorem can_step_pmono:
  forall p1 p2 (PS: forall s, p1 s ⊆ p2 s)
         xs xs' (CS: can_step p1 (xs',xs)),
  can_step p2 (xs',xs).
Proof.
  intros. inversion CS; subst. econstructor.
    apply PS, LU.
    apply XS.
Qed.

Theorem exec_prog_pmono:
  forall p1 p2 (PS: forall s, p1 s ⊆ p2 s)
         t (XP: exec_prog p1 t),
  exec_prog p2 t.
Proof.
  intros. induction t.
    apply exec_prog_nil.
    apply exec_prog_step.
      eapply IHt, exec_prog_tail, XP.
      destruct t as [|xs t].
        exact I.
        eapply can_step_pmono.
          exact PS.
          eapply exec_prog_final, XP.
Qed.

(* exec_stmt never deletes variables from typing contexts. *)
Theorem exec_stmt_cmono:
  forall v c s q c' s' x (XS: exec_stmt c s q c' s' x) (H: c' v = None),
  c v = None.
Proof.
  intros. dependent induction XS; try assumption.
    destruct (v == v0).
      subst v0. rewrite update_updated in H. discriminate.
      rewrite <- H, update_frame by assumption. reflexivity.
    apply IHXS, H.
    apply IHXS1, IHXS2, H.
    apply IHXS, H.
    apply IHXS, H.
Qed.

(* eval_exp, exec_stmt, and exec_prog ignore the values of variables not in the
   typing context. *)

Definition memacc_respects_typctx (c:typctx) :=
  forall s1 s2, reset_vars c s1 s2 = s1 ->
  (mem_readable s1 = mem_readable s2) /\
  (mem_writable s1 = mem_writable s2).

Definition in_ctx (c:typctx) v := if c v then true else false.

Lemma reset_vars_fchoose:
  forall c, reset_vars c = fchoose (in_ctx c).
Proof.
  intros. extensionality s1. extensionality s2. extensionality v.
  unfold reset_vars, fchoose, in_ctx. destruct (c v); reflexivity.
Qed.

Lemma reset_vars_sup_l:
  forall c1 c2 s1 s2
    (H: forall v, Bool.le (in_ctx c1 v) (in_ctx c2 v)),
  reset_vars c1 (reset_vars c2 s1 s2) s2 = reset_vars c2 s1 s2.
Proof.
  intros. rewrite !reset_vars_fchoose. apply fchoose_sup_l. assumption.
Qed.

Lemma reset_vars_revert:
  forall c s s', reset_vars c s' (reset_vars c s s') = s'.
Proof.
  intros. rewrite !reset_vars_fchoose. apply fchoose_revert.
Qed.

Lemma reset_vars_overwrite_l:
  forall c s1 s2 s3,
  reset_vars c (reset_vars c s1 s2) s3 = reset_vars c s1 s3.
Proof.
  intros. rewrite !reset_vars_fchoose. apply fchoose_overwrite_l.
Qed.

Lemma reset_vars_overwrite_r:
  forall c s1 s2 s3,
  reset_vars c s1 (reset_vars c s2 s3) = reset_vars c s1 s3.
Proof.
  intros. rewrite !reset_vars_fchoose. apply fchoose_overwrite_r.
Qed.

Lemma reset_vars_update_distr:
  forall c s1 s2 v n,
  reset_vars c s1 s2[v:=n] = reset_vars c (s1[v:=n]) (s2[v:=n]).
Proof.
  intros. rewrite !reset_vars_fchoose. apply fchoose_update_distr.
Qed.

Lemma reset_vars_update_c:
  forall c s1 s2 v y n,
  (reset_vars (c[v:=y]) s1 s2)[v:=n] = (reset_vars c s1 s2)[v:=n].
Proof.
  intros. rewrite !reset_vars_fchoose.
  replace (in_ctx _) with ((in_ctx c)[v:=if y then true else false]).
  apply fchoose_update_c.
  extensionality v'. unfold in_ctx. destruct (v' == v).
    subst v'. rewrite !update_updated. reflexivity.
    rewrite !update_frame by assumption. reflexivity.
Qed.

Theorem eval_exp_cframe:
  forall c (MRC: memacc_respects_typctx c) s1 s2 e n w
    (RV: reset_vars c s1 s2 = s1)
    (EE: eval_exp c s1 e n w),
  eval_exp c s2 e n w.
Proof.
  intros. revert s2 RV. dependent induction EE; intros;
  try (econstructor; try solve [ assumption
  | (apply IHEE1 + apply IHEE2 + apply IHEE3 + apply IHEE); assumption ]).

    rewrite <- RV. unfold reset_vars. rewrite TYP. apply EVar. assumption.
    intros n LEN. rewrite <- (proj1 (MRC _ _ RV)). apply R. assumption.
    intros n LEN. rewrite <- (proj2 (MRC _ _ RV)). apply W. assumption.
    apply IHEE2.
      intros s1' s2' RV'. apply MRC. rewrite <- RV'. apply reset_vars_sup_l.
        intro v'. unfold in_ctx. destruct (v' == v).
          subst v'. rewrite update_updated. destruct (c v); reflexivity.
          rewrite update_frame by assumption. destruct (c v'); reflexivity.
      rewrite <- reset_vars_update_distr, reset_vars_update_c, RV. reflexivity.
Qed.

Theorem exec_stmt_cframe:
 forall c (MRC: memacc_respects_typctx c) s1 s2 q c' s' x
   (RV: reset_vars c s1 s2 = s1)
   (XS: exec_stmt c s1 q c' s' x),
 exec_stmt c s2 q c' (reset_vars c' s2 s') x.
Proof.
  intros.
  revert s2 RV. dependent induction XS; intros;
    try (rewrite <- RV, reset_vars_revert).

    apply XNop.
    replace (reset_vars _ _ _) with (s2[v:=n]). apply XMove.
      eapply eval_exp_cframe; eassumption.
      extensionality v'. unfold reset_vars. destruct (v' == v).
        subst v'. rewrite !update_updated. reflexivity.
        rewrite !update_frame by assumption.
          destruct (c v') eqn:CV'; [|reflexivity].
          rewrite update_frame, <- RV by assumption. unfold reset_vars. rewrite CV'. reflexivity.
    eapply XJmp. eapply eval_exp_cframe; eassumption.
    apply XExn.
    apply XSeq1. apply IHXS; assumption.

    eapply XSeq2.
      apply IHXS1; assumption.
      eenough (H': reset_vars c' s0 s' = _). rewrite H'. eapply IHXS2.

        intros s1' s2' RV'. apply MRC. extensionality v'.
        assert (M1:=exec_stmt_cmono v' _ _ _ _ _ _ XS1).
        unfold reset_vars. destruct (c v') eqn:CV'; [|reflexivity].
        rewrite <- RV'. unfold reset_vars. destruct (c2 v').
          reflexivity.
          discriminate M1. reflexivity.

        extensionality v'.
        assert (M2:=exec_stmt_cmono v' _ _ _ _ _ _ XS2).
        unfold reset_vars.
        destruct (c2 v') eqn:C2V'; [|reflexivity].
        rewrite C2V'. reflexivity.

        extensionality v'.
        assert (M2:=exec_stmt_cmono v' _ _ _ _ _ _ XS2).
        unfold reset_vars.
        destruct (c' v') eqn:C'V'. reflexivity.
        rewrite M2; reflexivity.

    eapply XIf.
      eapply eval_exp_cframe; eassumption.
      apply IHXS; assumption.
    eapply XRep.
      eapply eval_exp_cframe; eassumption.
      apply IHXS; assumption.
Qed.

Theorem exec_prog_map:
  forall f p t
    (CS: forall xs' xs, can_step p (xs',xs) -> can_step p (f xs', f xs))
    (XP: exec_prog p t),
  exec_prog p (map f t).
Proof.
  intros. apply Forall_forall. intros (xs',xs) IN'.
  apply In_ith in IN'. destruct IN' as [i IN'].
  apply Forall_ith with (i:=i) in XP.
  destruct (ith (stepsof t) i) as [(xs0',xs0)|] eqn:H.

    rewrite ith_stepsof in IN'.
    destruct (skipn i _) as [|xs1 l1] eqn:H1. discriminate.
    destruct l1 as [|xs2 l2] eqn:H2. discriminate.
    inversion IN'; clear IN'; subst.
    rewrite skipn_map in H1.
    rewrite ith_stepsof in H.
    destruct (skipn i t) as [|xs1' l1'] eqn:H1'. discriminate.
    destruct l1' as [|xs2' l2'] eqn:H2'. discriminate.
    inversion H; clear H; subst.
    inversion H1; clear H1; subst.
    apply CS. assumption.

    contradict H. apply ith_Some.
    erewrite length_stepsof, <- length_map, <- length_stepsof.
    apply ith_Some. rewrite IN'. discriminate.
Qed.

Theorem exec_prog_cframe:
  forall p t s0
    (MRC: memacc_respects_typctx archtyps)
    (CODEACC: forall s, p s = p (reset_temps s0 s))
    (XP: exec_prog p t),
  exec_prog p (map (fun (xs:exit*store) => let (x,s) := xs in
    (x, reset_temps s0 s)) t).
Proof.
  intros. apply exec_prog_map; [|assumption].
  intros (x',s') (x,s) CS. inversion CS; clear CS; subst.

  eenough (H: reset_temps _ _ = _).
    rewrite H. eapply CanStep.
      rewrite <- CODEACC. eassumption.
      eapply exec_stmt_cframe in XS. exact XS. assumption.
      apply reset_vars_revert.

    unfold reset_temps.
    rewrite reset_vars_overwrite_l, reset_vars_overwrite_r.
    extensionality v. unfold reset_vars.
    assert (M':=exec_stmt_cmono v _ _ _ _ _ _ XS).
    destruct (archtyps v) eqn:CV; [|reflexivity].
    destruct (c' v). reflexivity. discriminate M'. reflexivity.
Qed.

End Monotonicity.



Section InvariantProofs.

(* To prove properties of states computed by repeat-loops, it suffices to prove
   that each loop iteration preserves the property. *)
Theorem rep_inv:
  forall (P: typctx -> store -> Prop)
         c s e q c' s' x (XS: exec_stmt c s (Rep e q) c' s' x) (PRE: P c s)
         (INV: forall c s c' s' x (PRE: P c s) (XS: exec_stmt c s q c' s' x), P c' s'),
  P c' s'.
Proof.
  intros. inversion XS; clear XS; subst.
  clear e w E. revert c s PRE XS0. apply Niter_invariant; intros.
    inversion XS0; subst. exact PRE.
    inversion XS0; subst.
      eapply INV; eassumption.
      eapply IH.
        eapply INV. exact PRE. exact XS1.
        exact XS2.
Qed.

(* To prove that a property holds for all states in a trace, it suffices to
   prove that the property is preserved by every statement in the program. *)
Theorem prog_inv_universal:
  forall (P: exit * store -> Prop) p t (XP: exec_prog p t)
         (PRE: match ostartof t with None => True | Some xs0 => P xs0 end)
         (INV: forall a1 s1 sz q c1' s1' x1 (IL: p s1 a1 = Some (sz,q)) (PRE: P (Addr a1,s1))
                      (XS: exec_stmt archtyps s1 q c1' s1' x1),
               P (exitof (a1 + sz) x1, reset_temps s1 s1')),
  Forall P t.
Proof.
  intros. induction t as [|xs' t]; intros.
    apply Forall_nil.
    apply Forall_cons.
      destruct t as [|xs t].
        apply PRE.
        assert (CS:=exec_prog_final _ _ _ _ XP). inversion CS; subst. eapply INV.
          exact LU.
          eapply Forall_inv, IHt.
            eapply exec_prog_tail, XP.
            rewrite ostartof_cons, startof_cons in PRE. exact PRE.
          exact XS.
      apply IHt.
        eapply exec_prog_tail, XP.
        destruct t.
          exact I.
          rewrite ostartof_cons, startof_cons in PRE. exact PRE.
Qed.

(* Alternatively, one may prove that the property is preserved by all the reachable traces.
   (The user's invariant may adopt a precondition of False for unreachable statements.) *)
Theorem prog_inv_reachable:
  forall (P: trace -> Prop) p t (XP: exec_prog p t)
         (PRE: P match ostartof t with None => nil | Some xs0 => xs0::nil end)
         (INV: forall a1 s1 sz q c1' s1' x1 t1 t2
                      (SPL: t = t2++((Addr a1,s1)::t1))
                      (PRE: P ((Addr a1,s1)::t1))
                      (IL: p s1 a1 = Some (sz,q))
                      (XS: exec_stmt archtyps s1 q c1' s1' x1),
               P ((exitof (a1 + sz) x1, reset_temps s1 s1')::(Addr a1,s1)::t1)),
  P t.
Proof.
  induction t as [|xs' t]; intros.
    exact PRE.
    destruct t as [|xs t].
      exact PRE.
      inversion XP. inversion H1. subst. eapply INV with (t2:=_::nil); [ | | eassumption..].
        simpl. reflexivity.
        apply IHt.
          exact H2.
          rewrite ostartof_cons, startof_cons in PRE. exact PRE.
          intros. eapply INV; [|eassumption..].
            rewrite SPL, app_comm_cons. reflexivity.
Qed.

(* Rather than assigning and proving an invariant at every machine instruction, we can generalize
   the above to allow users to assign invariants to only a few machine instructions.  To prove that
   all the invariants are satisfied, the user can prove that any execution that starts in an
   invariant-satisfying state and that reaches another invariant always satisfies the latter. *)

(* The "effective invariant" at a code point is usually just the invariant
   placed there if b=true, or no invariant if b=false (which signals that this is
   the start invariant, so it can't be its own "next" invariant.)
   However, there are four special cases:  If the trace ...
      (a) is at a hardware exception,
      (b) is at a user-defined exit point,
      (c) has left the code section, or
      (d) is nil (not a valid trace),
   then an invariant is forced at this location.  If the user's invariant set (Invs)
   already supplies an invariant, then use it (even if b=false); otherwise use False. *)
Definition effinv' (p:program) (xp:trace->bool) t (P:Prop) :=
  if xp t then Some P else
  match t with (Addr a,s)::_ => if p s a then None else Some P
             | _ => Some P end.
Definition effinv (b:bool) (p:program) Inv (xp:trace->bool) t :=
  match Inv t with
  | None => effinv' p xp t False
  | Some P => if b then Some P else effinv' p xp t P
  end.
Global Arguments effinv' p xp / !t.
Global Arguments effinv b p Inv xp / !t.

(* The "next invariant" property is true if the computation always eventually
   reaches a "next" invariant, and in a state that satisfies that invariant.
   (If the computation is already at an invariant, it is considered its own "next"
   invariant if parameter b=true; otherwise the computation must take at least
   one step before it can satisfy the "next invariant" property.) *)
CoInductive nextinv' p Invs (xp: trace -> bool): bool -> trace -> Prop :=
| NIHere' (b:bool) t
    (TRU: true_inv (effinv b p Invs xp t)):
    nextinv' p Invs xp b t
| NIStep' b a s t sz q
          (NOI: effinv b p Invs xp ((Addr a, s)::t) = None)
          (IL: p s a = Some (sz,q))
          (STEP: forall c1 s1 x1 (XS: exec_stmt archtyps s q c1 s1 x1),
                 nextinv' p Invs xp true ((exitof (a+sz) x1, reset_temps s s1)::(Addr a,s)::t)):
    nextinv' p Invs xp b ((Addr a, s)::t).

(* Proving the "next invariant satisfied" property for all invariant points proves partial
   correctness of the program. *)

Definition satisfies_all p Invs xp t : Prop :=
  exec_prog p t -> unterminated xp (tl t) -> forall b, nextinv' p Invs xp b t.

Theorem satall_trueif_inv:
  forall p Invs xp t
    (SA: satisfies_all p Invs xp t) (XP: exec_prog p t) (UT: unterminated xp (tl t)),
  trueif_inv (Invs t).
Proof.
  unfold satisfies_all. intros. specialize (SA XP UT true). inversion SA; subst.
    unfold effinv,effinv' in TRU. destruct (Invs t). assumption.
      destruct (xp t). contradiction.
      destruct t. contradiction.
      destruct p0 as ([a|i],s). destruct (p s a); contradiction. contradiction.
    unfold effinv,effinv' in NOI. destruct (Invs _). discriminate. exact I.
Qed.

Lemma nextinv_noinv:
  forall p Invs xp b t (NI: nextinv' p Invs xp true t)
    (NOI: effinv true p Invs xp t = None),
  nextinv' p Invs xp b t.
Proof.
  intros. destruct b. exact NI. inversion NI; subst.
    rewrite NOI in TRU. contradiction.
    eapply NIStep'; try eassumption. unfold effinv in *.
      destruct (Invs _). discriminate. assumption.
Qed.

Lemma nextinv_raise:
  forall p Invs xp b i s t,
  match Invs ((Raise i,s)::t) with None => False | Some P => P end <->
  nextinv' p Invs xp b ((Raise i,s)::t).
Proof.
  split; intro H.

    apply NIHere'. unfold effinv, effinv'.
    destruct (Invs _); [|contradiction].
    destruct b; [|destruct (xp _)]; assumption.

    inversion H; subst. unfold effinv, effinv' in TRU.
    destruct (Invs _).
      destruct b; [|destruct (xp _)]; assumption.
      destruct (xp _); assumption.
Qed.

Lemma nextinv_nil:
  forall p Invs xp b (NI: nextinv' p Invs xp true nil),
  nextinv' p Invs xp b nil.
Proof.
  intros. destruct b. assumption.
  inversion NI; subst. simpl in TRU.
  apply NIHere'. simpl.
  destruct (Invs nil); [destruct (xp nil)|]; assumption.
Qed.

Lemma nextinv_exit:
  forall p Invs xp b t (NI: nextinv' p Invs xp true t)
    (XP: xp t = true),
  nextinv' p Invs xp b t.
Proof.
  intros. destruct b. assumption.
  apply NIHere'. inversion NI; subst.
    unfold effinv,effinv' in *. rewrite XP in *. assumption.
    simpl in NOI. rewrite XP in NOI. destruct (Invs _); discriminate.
Qed.

Lemma nextinv_nocode:
  forall p Invs xp b a s t (NI: nextinv' p Invs xp true ((Addr a,s)::t))
    (IL: p s a = None),
  nextinv' p Invs xp b ((Addr a,s)::t).
Proof.
  intros. destruct b. assumption.
  apply NIHere'. inversion NI; subst.
    unfold effinv,effinv' in *. rewrite IL in *.
      destruct (Invs _); [destruct (xp _)|]; assumption.
    rewrite IL0 in IL. discriminate.
Qed.

Lemma nextinv_allcases:
  forall p Invs xp b t (NI: nextinv' p Invs xp true t)
    (H: match t with (Addr a,s)::_ =>
          forall (NXP: xp t = false) (IL: p s a <> None) (TRU: true_inv (Invs t)),
            nextinv' p Invs xp false t
        | _ => True end),
  nextinv' p Invs xp b t.
Proof.
  intros. destruct b. assumption.
  destruct t as [|([a|i],s) t].
    apply nextinv_nil. assumption.
    destruct (effinv true p Invs xp ((Addr a,s)::t)) eqn:EI.
      simpl in EI. destruct (xp ((Addr a,s)::t)) eqn:XP.
        apply nextinv_exit; assumption.
        destruct (p s a) eqn:IL.
          destruct (Invs _) eqn:INV.
            apply H. reflexivity. discriminate 1. inversion NI; subst.
              simpl in TRU. rewrite INV in TRU. assumption.
              simpl in NOI. rewrite INV in NOI. discriminate.
            discriminate.
          apply nextinv_nocode; assumption.
      apply nextinv_noinv; assumption.
    apply nextinv_raise. inversion NI; subst.
      simpl in TRU. destruct (Invs _). assumption. destruct (xp _); assumption. 
Qed.

Theorem prove_invs':
  forall p Invs xp t
         (PRE: nextinv' p Invs xp true match ostartof t with None => nil | Some xs0 => xs0::nil end)
         (INV: forall t1 a1 s1 t2
                      (SPL: t = (t2++(Addr a1,s1)::t1))
                      (XP: exec_prog p ((Addr a1,s1)::t1))
                      (UT: unterminated xp t1)
                      (PRE: true_inv (get_precondition p Invs xp a1 s1 t1)),
               nextinv' p Invs xp false ((Addr a1,s1)::t1)),
  satisfies_all p Invs xp t.
Proof.
  unfold get_precondition. intros. intros XP UT.
  assert (SPL: exists t', t = t'++t). exists nil. reflexivity.
  revert SPL UT. pattern t at -1. eapply prog_inv_reachable. exact XP.

    intros. apply nextinv_allcases. destruct t; assumption.
    destruct t as [|xs' t]. exact I.
    simpl. destruct (startof t xs') as ([a0|i],s0) eqn:ST; [|exact I].
    intros. destruct (p s0 a0) eqn:IL'; [|contradict IL; reflexivity].
    eapply INV with (t2 := removelast (xs'::t)).
      rewrite <- ST. simpl. destruct t. reflexivity. unfold startof.
        rewrite <- app_comm_cons, <- app_removelast_last by discriminate. reflexivity.
      apply Forall_nil.
      apply UT.
      rewrite NXP,IL'. assumption.

    intros.
    assert (INV' := INV _ _ _ _ SPL). rewrite IL in INV'.
    simpl in UT. inversion UT; subst. clear UT.
    eenough (H:_); [ apply PRE0 with (b:=b) in H; [clear PRE0 | eexists;reflexivity]
                   | apply H2 ].
    rewrite H1 in INV'.
    inversion H; clear H; subst.

      simpl in TRU. rewrite H1,IL in TRU.
      destruct (Invs _) eqn:INVeq; [|contradiction].
      destruct b; [|contradiction].
      apply INV' in TRU.
        inversion TRU; subst.
          simpl in TRU0. rewrite INVeq,H1,IL in TRU0. contradiction.
          rewrite IL in IL0. inversion IL0; subst. eapply STEP. exact XS.
        apply exec_prog_split in XP. apply XP.
        apply H2.

      rewrite IL0 in IL. inversion IL; subst. clear IL.
      destruct b. eapply STEP. exact XS.
      apply nextinv_allcases. eapply STEP; eassumption.
      destruct (exitof _ _) as [a'|i] eqn:EO; [|exact I]. intros.
      destruct SPL0 as [t' SPL]. apply INV with (t2:=t').
        assumption.
        rewrite <- EO. apply exec_prog_step.
          apply exec_prog_split in XP. apply XP.
          eapply CanStep; eassumption. apply unterminated_cons; assumption.
        replace (xp _) with false; [idtac].
          destruct (p _ a'). assumption. contradict IL. reflexivity.
Qed.

(* As long as the exit points are fixed (i.e., they depend on the current location,
   not the history of the trace), then trace histories can be shifted out of nextinv
   arguments into the invariant set function argument. *)
Theorem nextinv_apptrace:
  forall p Invs xp b t1 t2 xs
    (XP: forall xs t, xp (xs::t++t1) = xp (xs::t))
    (NI: nextinv' p (fun t => Invs match t with nil => nil | _ => t++t1 end) xp b (xs::t2)),
  nextinv' p Invs xp b (xs::t2++t1).
Proof.
  intros. revert b xs t2 NI. cofix IH; intros. inversion NI; subst.
    apply NIHere'. simpl. rewrite XP. exact TRU.
    eapply NIStep'.
      simpl. rewrite XP. apply NOI.
      exact IL.
      intros. rewrite app_comm_cons. eapply IH, STEP, XS.
Qed.

(* The following modifications to effective invariants preserve nextinv properties:
   1. Invariants may be removed.
   2. Always-true invariants may be added.
   3. Invariant P may be weakened to Q if P -> Q. *)
Definition effinv_impl (Inv1 Inv2:option Prop) (Goal:Prop) :=
  match Inv1, Inv2 with
  | None,None => True (* no change *)
  | Some P,None => P -> Goal (* remove goal-implying invariant *)
  | None,Some P => P  (* add tautological invariant *)
  | Some P,Some Q => P -> Q (* weaken invariant *)
  end.

Lemma effinv_cases:
  forall p Invs1 Invs2 xp1 xp2 (Goal:Prop) b t
    (EI: effinv_impl (effinv true p Invs1 xp1 t) (effinv true p Invs2 xp2 t) True)
    (CASE1: xp1 t = true -> xp2 t = false -> true_inv (Invs1 t) -> Goal)
    (CASE2: xp1 t = false -> xp2 t = false -> b = true -> Invs2 t = None ->
            match t with (Addr a,s)::_ => p s a <> None | _ => False end ->
            true_inv (Invs1 t) -> Goal)
    (CASE3: xp1 t = false -> xp2 t = true -> b = false -> trueif_inv (Invs1 t) \/ true_inv (Invs2 t)),
  effinv_impl (effinv b p Invs1 xp1 t) (effinv b p Invs2 xp2 t) Goal.
Proof.
  unfold trueif_inv, effinv, effinv', effinv_impl. intros.
  repeat first
  [ assumption | exact I | intro; contradiction
  | match goal with |- match match ?x with _ => _ end with _ => _ end => destruct x end
  | apply CASE1; reflexivity
  | destruct CASE3; solve [ reflexivity | assumption | apply EI; assumption ]
  ].

  destruct (xp1 _).
    apply CASE1; reflexivity.
    apply CASE2; solve [ reflexivity | assumption | discriminate 1 ].
Qed.

(* Assert that property P is satisfied after every possible step of trace t. *)
Definition afterstep p t P : Prop :=
  forall a s c1 s1 x1 sz q
    (H: hd_error t = Some (Addr a,s))
    (IL: match t with (Addr a,s)::_ => p s a | _ => None end = Some (sz,q))
    (XS: exec_stmt archtyps s q c1 s1 x1),
  P ((exitof (a+sz) x1, reset_temps s s1) :: t).

(* Effective invariant implication (effinv_impl) is sound. *)
Theorem nextinv_impl_invs (P:trace->Prop):
  forall p Invs1 Invs2 xp1 xp2 xs t1
    (BC: P nil)
    (IC: forall t1 xs t2 (H1: P (tl (t2++xs::nil))) (H2: xp1 (t2++xs::t1) = false),
           P (t2++xs::nil))
    (IMP: forall t2 (XP: exec_prog p (t2++xs::nil)) (IH: P (tl (t2++xs::nil))),
          effinv_impl (effinv true p Invs1 xp1 (t2++xs::t1))
                      (effinv true p Invs2 xp2 (t2++xs::t1))
            (nextinv' p Invs2 xp2 true (t2++xs::t1) \/
             P (t2++xs::nil) /\ afterstep p (t2++xs::t1) (nextinv' p Invs1 xp1 true)))
    (NI: nextinv' p Invs1 xp1 true (xs::t1)),
  nextinv' p Invs2 xp2 true (xs::t1).
Proof.
  intros.
  set (t2 := @nil (exit*store)).
  change (xs::t1) with (t2++xs::t1) in NI |- *.
  assert (XP: exec_prog p (t2++xs::nil)) by apply Forall_nil.
  change nil with (tl (t2++xs::nil)) in BC.
  clearbody t2.
  revert t2 NI XP BC. cofix IH; intros. inversion NI; subst.

    specialize (IMP t2 XP BC).
    destruct (effinv true p Invs2 xp2 (t2++xs::t1)) eqn:EI2; [apply NIHere'|];
    unfold effinv,effinv',effinv_impl in *;
    repeat first
    [ solve [ apply IMP;assumption | discriminate | contradiction ]
    | match type of EI2 with Some _ = Some _ => inversion EI2; clear EI2; subst end
    | match goal with |- true_inv match ?x with _ => _ end => destruct x eqn:? end
    | match type of TRU with true_inv match ?x with _ => _ end => destruct x eqn:? end
    | match type of EI2 with match ?x with _ => _ end = _ => destruct x eqn:? end
    ].
    destruct (IMP TRU). assumption.
    destruct p1 as (sz,q). eapply NIStep';[|eassumption|].
      unfold effinv. rewrite Heqo0. unfold effinv'. rewrite Heqb,Heqo1. reflexivity.
      intros. rewrite <- Heql. rewrite app_comm_cons. apply IH; simpl.
        rewrite Heql. eapply H; try solve [ eassumption | reflexivity ].
        apply exec_prog_step. assumption. destruct t2;
          simpl in Heql |- *; inversion Heql; eapply CanStep; eassumption.
        apply H.

    assert (IMP' := IMP t2 XP BC). rewrite H1 in NOI.
    destruct (effinv true p Invs2 xp2 (t2++xs::t1)) eqn:EI2;
    [ apply NIHere' | eapply NIStep'; [|eassumption|shelve] ]; rewrite H1;
    unfold effinv,effinv',effinv_impl in *;
    repeat first
    [ solve [ reflexivity | discriminate | assumption ]
    | match type of EI2 with Some _ = Some _ => inversion EI2; clear EI2; subst end
    | match goal with |- match ?x with _ => _ end => destruct x end
    | match type of IMP' with match match ?x with _ => _ end with _ => _ end => destruct x end
    | match type of EI2 with match ?x with _ => _ end = _ => destruct x end
    ].

    Unshelve. intros. rewrite H1, app_comm_cons. apply IH; simpl.
      rewrite <- H1. eapply STEP. eassumption.
      apply exec_prog_step. assumption. destruct t2 as [|xs' t2];
        simpl; injection H1; intros; subst t; rewrite <- H0; eapply CanStep; eassumption.
      apply IC with (t1:=t1). assumption. clear - NOI. unfold effinv,effinv' in NOI.
        destruct (Invs1 _). discriminate. destruct (xp1 _). discriminate. reflexivity.
Qed.

(* Sufficient conditions whereby a caller with one invariant+exit set
   can safely call a callee with a different invariant+exit set:
   (1) The callee's invariants must imply any colocated caller
       invariants (e.g., callee-only invariants imply True).
   (2) The callee must not exit other than by reaching the return site
       (e.g., not by raising a hardware exception or jumping to a
       non-code address).
   (3) Caller and callee invariants must be functions of the current
       cpu state, not the history of the trace. *)
Definition may_call
    (p:program)
    (caller_Invs: trace -> option Prop) (caller_xp: trace -> bool)
    (callee_Invs: trace -> option Prop) (callee_xp: trace -> bool) : Prop
:=
  (forall (t:trace),
   effinv_impl (effinv true p callee_Invs callee_xp t)
               (effinv true p caller_Invs caller_xp t) True /\
   match t with
   | nil => callee_xp t
   | (Raise _,_)::_ => if callee_Invs t then true else callee_xp t
   | (Addr a,s)::_ => if p s a then false else callee_xp t
   end = false) /\
  (forall xs t, callee_Invs (xs::t) = callee_Invs (xs::nil)) /\
  (forall xs t, callee_xp (xs::t) = callee_xp (xs::nil)).

(* Perform a call by replacing the current nextinv goal at a callee entry point
   with a set of new goals, one for each callee exit point. *)
Theorem exec_subroutine:
  forall p Invs1 xp1 Invs2 xp2 a1 s1 t1
         (CALLEE: forall t xs' (ENTRY: startof t xs' = (Addr a1, s1)),
                  satisfies_all p Invs2 xp2 (xs'::t))
         (MC: may_call p Invs1 xp1 Invs2 xp2)
         (POST: forall a' s' t2
                  (ENTRY: startof t2 (Addr a', s') = (Addr a1, s1))
                  (XP: exec_prog p ((Addr a',s')::t2))
                  (UT: unterminated xp2 t2)
                  (PRE: true_inv (get_postcondition p Invs2 xp2 a' s' (t2++t1))),
               nextinv' p Invs1 xp1 true ((Addr a',s')::t2++t1)),
  nextinv' p Invs1 xp1 true ((Addr a1,s1)::t1).
Proof.
  intros.
  destruct MC as [H [CI1 CI2]].
  eassert (IMP: forall (t:trace), _). intro. exact (proj1 (H t)).
  eassert (INVXP2: forall (t:trace), _). intro. exact (proj2 (H t)).
  apply nextinv_impl_invs with (Invs1:=Invs2) (xp1:=xp2) (P:=unterminated xp2).
    apply ForallPrefixes_nil, (proj2 (H nil)).
    intros. destruct t2; simpl in H2 |- *; apply unterminated_cons;
      rewrite CI2 in H2; try rewrite CI2; assumption.
  clear H. intros.
  change (t2++(Addr a1,s1)::t1) with (t2++(Addr a1,s1)::nil++t1).
  rewrite app_comm_cons, app_assoc. rename t2 into t2'.
  set (xs := hd (Addr a1,s1) t2'). set (t2 := tl (t2'++(Addr a1,s1)::nil)) in IH.
  replace (t2'++(Addr a1,s1)::nil) with (xs::t2) in XP |- * by
    (destruct t2'; reflexivity).
  assert (ENTRY: startof t2 xs = (Addr a1, s1)).
    destruct t2'. reflexivity. apply startof_niltail.
  clearbody xs t2. clear t2'. rewrite <- app_comm_cons.
  assert (INVXP2' := INVXP2 (xs::t2++t1)). destruct xs as (x,s). simpl in INVXP2'.
  apply effinv_cases; intros. apply IMP.

    (* Drop callee exit and continue to return to caller. *)
    left. destruct x as [a|i].
      eapply POST. apply ENTRY. apply XP. apply IH.
        unfold get_postcondition. rewrite H. destruct (p s a) eqn:IL.
          destruct (Invs2 _). assumption. exact I.
          rewrite H in INVXP2'. discriminate.
      destruct (Invs2 _); rewrite INVXP2' in H; discriminate.

    (* Drop callee internal invariant. *)
    right. split. apply unterminated_cons.
      rewrite CI2 in H |- *. assumption.
      assumption.
    unfold afterstep. intros. rewrite app_comm_cons. apply nextinv_apptrace.
      intros. rewrite CI2. symmetry. apply CI2.
      match goal with |- nextinv' _ ?f _ _ _ => replace f with Invs2 end.
        apply CALLEE.
          rewrite startof_cons. assumption.
          apply exec_prog_step.
            assumption.
            inversion H5; subst. eapply CanStep; eassumption.
          apply unterminated_cons.
            rewrite CI2 in H |- *. apply H.
            assumption.
        extensionality t. destruct t. reflexivity. rewrite CI1. symmetry. apply CI1.

    (* This case can only happen if the callee's entry point is a caller
       exit point. Our theorem only applies when we've taken at least one
       step to get from caller to callee (b=true), so this is a contradiction. *)
    discriminate.

  change ((Addr a1,s1)::t1) with (((Addr a1,s1)::nil)++t1).
  apply nextinv_apptrace. intros. rewrite (CI2 _ t). apply CI2.
  match goal with |- nextinv' _ ?f _ _ _ => replace f with Invs2 end.
    apply CALLEE. reflexivity. apply Forall_nil. apply ForallPrefixes_nil. apply (INVXP2 nil).
    extensionality t. specialize (INVXP2 t). destruct t. reflexivity. simpl. rewrite (CI1 _ (_++_)). apply CI1.
Qed.

(* When proving nextinv in practice, it's convenient to retain a hidden exec_prog
   hypothesis that rememembers that the current trace is a valid execution.  This
   facilitates proving premises of subroutine calls (e.g., "models"). We therefore
   define exported versions of nextinv and its constructors that retain exec_prog. *)
Definition nextinv p Invs xp b t : Prop :=
  forall (XP: exec_prog p t), nextinv' p Invs xp b t.

Theorem exec_prog_nextinv:
  forall p Invs xp b t,
    (forall (XP: exec_prog p t), nextinv p Invs xp b t) ->
    nextinv p Invs xp b t.
Proof. intros. intro XP. apply H; assumption. Qed.

Theorem NIHere:
  forall p Invs xp (b:bool) t
    (TRU: true_inv (effinv b p Invs xp t)),
    nextinv p Invs xp b t.
Proof.
  unfold nextinv. intros. apply NIHere'. assumption.
Qed.

Theorem NIStep:
  forall p Invs xp b a s t sz q
         (NOI: effinv b p Invs xp ((Addr a, s)::t) = None)
         (IL: p s a = Some (sz,q))
         (STEP: forall c1 s1 x1 (XS: exec_stmt archtyps s q c1 s1 x1),
                nextinv p Invs xp true ((exitof (a+sz) x1, reset_temps s s1)::(Addr a,s)::t)),
  nextinv p Invs xp b ((Addr a,s)::t).
Proof.
  unfold nextinv. intros. eapply NIStep'; try eassumption.
  intros. eapply STEP. eassumption.
  apply exec_prog_step. assumption. eapply CanStep; eassumption.
Qed.

Theorem NIStep_unterminated:
  forall p Invs xp b a s t sz q
         (NOI: effinv b p Invs xp ((Addr a, s)::t) = None)
         (IL: p s a = Some (sz,q))
         (STEP: forall c1 s1 x1 (XS: exec_stmt archtyps s q c1 s1 x1)
                  (UT: unterminated xp ((Addr a,s)::t)),
                nextinv p Invs xp true ((exitof (a+sz) x1, reset_temps s s1)::(Addr a,s)::t)),
  unterminated xp t -> nextinv p Invs xp b ((Addr a,s)::t).
Proof.
  intros. eapply NIStep; try eassumption.
  intros. eapply STEP. eassumption.
  apply ForallPrefixes_cons; [|apply H].
  unfold effinv, effinv' in NOI.
  destruct (xp _); [|reflexivity].
  destruct (Invs _); [destruct b|]; discriminate.
Qed.

Lemma nextinv_here:
  forall p Invs (xp: trace -> bool) b t P
         (INV: effinv b p Invs xp t = Some P)
         (TRU: P),
    nextinv p Invs xp b t.
Proof.
  intros. apply NIHere. rewrite INV. assumption.
Qed.

Theorem prove_invs:
  forall p Invs xp t
         (PRE: nextinv p Invs xp true match ostartof t with None => nil | Some xs0 => xs0::nil end)
         (INV: forall t1 a1 s1 t2
                      (UT: unterminated xp t1)
                      (SPL: t = (t2++(Addr a1,s1)::t1))
                      (PRE: true_inv (get_precondition p Invs xp a1 s1 t1)),
               nextinv p Invs xp false ((Addr a1,s1)::t1)),
  satisfies_all p Invs xp t.
Proof.
  unfold nextinv, satisfies_all. intros. apply prove_invs'; try assumption.
    apply forallprefixes_nil_inv in H0. apply PRE; destruct (ostartof t); constructor; assumption.
    intros. eapply INV; eassumption.
Qed.

(* If your current goal is a nextinv, and you've already proved a lemma L with conclusion
   satisfies_all, use "eapply use_satall_lemma" to get L's invariant as a hypothesis.
   Typical usage:
     eapply use_satall_lemma. eassumption.
     apply L. (* prove any of L's hypotheses here *)
     intro H. simpl in H. *)
Theorem use_satall_lemma:
  forall p Invs Invs' xp b t
    (UT: unterminated xp (tl t))
    (SA: satisfies_all p Invs xp t)
    (H: forall (INV: trueif_inv (Invs t)), nextinv p Invs' xp b t),
  nextinv p Invs' xp b t.
Proof.
  intros. intro XP. apply H; [|exact XP].
  eapply satall_trueif_inv; eassumption.
Qed.

(* If your current goal is a nextinv, and you've already proved a lemma L with conclusion
   forall_endstates, use "eapply use_endstates_lemma" to get L's conclusion as a hypothesis.
   Typical usage:
     eapply use_endstates_lemma. eassumption.
     apply L. (* prove any of L's hypotheses here *)
     intro H. simpl in H. *)
Theorem use_endstates_lemma:
  forall P p Invs xp b t x x' s s'
    (ENTRY: startof t (x',s') = (x,s))
    (FE: forall_endstates p P)
    (H: forall (INV: P x s x' s'), nextinv p Invs xp b ((x',s')::t)),
  nextinv p Invs xp b ((x',s')::t).
Proof.
  intros. intro XP. apply H; [|exact XP].
  eapply FE; eassumption.
Qed.

(* Introduce a convenient logic for subroutine calls. *)

Definition inv_type T := N -> Prop -> T.
Definition invariant_set :=
  forall T, (inv_type T) -> (inv_type T) -> T -> store -> addr -> T.

Definition same_invset_family (f g:invariant_set) : Prop :=
  f _ (fun n _ => Some(false,n)) (fun n _ => Some(true,n)) None =
  g _ (fun n _ => Some(false,n)) (fun n _ => Some(true,n)) None.

Definition make_exits (n:N) (p:program) (f:invariant_set) (t:trace) : bool :=
  match t with nil | (Raise _,_)::_ => false | (Addr a,s)::_ =>
    if p s a then
      match f _ (fun m _ => Some(false,m)) (fun m _ => Some(true,m)) None s a with
      | Some (true,m) => N.eqb m n
      | _ => false
      end
    else false
  end.

Definition make_invs (n:N) (p:program) (f:invariant_set) (t:trace) : option Prop :=
  match t with nil | (Raise _,_)::_ => None | (Addr a,s)::_ =>
    if p s a then
      match f _ (fun m _ => Some(false,m)) (fun n _ => Some(true,n)) None s a
      with None => None | Some(_,m) =>
        match m ?= n with Eq => Some (f _ (fun _ P => P) (fun _ P => P) False s a) | Lt => None | Gt => Some False end
      end
    else None
  end.

Theorem simple_may_call:
  forall p (f g:invariant_set) (n m:N) (SF: same_invset_family f g) (H: m <? n = true),
  may_call p (make_invs n p f) (make_exits n p f)
             (make_invs m p g) (make_exits m p g).
Proof.
  repeat split.

  destruct t as [|(e,s) t]. intro. assumption.
  destruct e as [a|i]; [|intro;assumption].
  simpl. destruct (p s a); [|intro;assumption].
  rewrite SF. destruct (g _ _ _ None s a) as [(b,n0)|]; [|exact I].
    destruct (n0 ?= m) eqn:CMP.
      apply N.compare_eq in CMP. subst n0.
        rewrite (proj2 (N.eqb_neq _ _)) by apply N.lt_neq, N.ltb_lt, H.
        unfold "<?" in H. destruct (m ?= n); try discriminate.
        destruct b; intro; exact I.
      apply N.ltb_lt in H. apply (proj1 (N.compare_lt_iff _ _)) in CMP. rewrite (proj2 (N.eqb_neq _ _)).
        rewrite (proj2 (N.compare_lt_iff _ _)).
          rewrite (proj2 (N.eqb_neq _ _)).
            destruct b; exact I.
            apply N.lt_neq. transitivity m; assumption.
          transitivity m; assumption.
        apply N.lt_neq, CMP.
      simpl. match goal with |- match ?x with _ => _ end => destruct x end;
        contradiction.

  destruct t as [|(e,s) t]. reflexivity.
  destruct e as [a|i]; [|reflexivity].
  simpl. destruct (p s a); reflexivity.
Qed.

Theorem perform_call n m (H: n <? m = true) f g p a1 s1 t1:
  forall (CALLEE: forall t xs' (ENTRY: startof t xs' = (Addr a1, s1)),
                  satisfies_all p (make_invs n p g) (make_exits n p g) (xs'::t))
         (SF: same_invset_family f g)
         (POST: forall a' s' t2
                  (ENTRY: startof t2 (Addr a', s') = (Addr a1, s1))
                  (XP: exec_prog p ((Addr a',s')::t2))
                  (UT: unterminated (make_exits n p g) t2)
                  (PRE: true_inv (get_postcondition p (make_invs n p g) (make_exits n p g) a' s' (t2++t1))),
               nextinv p (make_invs m p f) (make_exits m p f) true ((Addr a',s')::t2++t1)),
  nextinv p (make_invs m p f) (make_exits m p f) true ((Addr a1,s1)::t1).
Proof.
  unfold nextinv. intros.
  eapply exec_subroutine.
    intros. apply CALLEE. exact ENTRY.
    apply simple_may_call; assumption.
    intros. apply POST; try assumption. rewrite app_comm_cons. apply exec_prog_app.
      eapply exec_prog_tail. eassumption.
      destruct t1. exact I. simpl. rewrite ENTRY. eapply exec_prog_final. eassumption.
      assumption.
Qed.

End InvariantProofs.



Section FrameTheorems.

(* Statements and programs that contain no assignments to some IL variable v
   leave that variable unchanged in the output store. *)

Theorem novar_noassign v:
  forall q, forall_vars_in_stmt (fun v0 => v0 <> v) q -> noassign v q.
Proof.
  induction q; intro; constructor; try ((apply IHq1 + apply IHq2 + apply IHq); split); apply H.
Qed.

Theorem noassign_stmt_same:
  forall v q (NA: noassign v q) c s s' c' x,
  exec_stmt c s q c' s' x -> (s v, c v) = (s' v, c' v).
Proof.
  induction q; intros; inversion H; subst; try reflexivity.
    inversion NA; subst. symmetry. rewrite !update_frame by apply not_eq_sym, PV. reflexivity.
    eapply IHq1; try eassumption. inversion NA. assumption.
    inversion NA. transitivity (s2 v, c2 v); [ eapply IHq1 | eapply IHq2 ]; eassumption.
    inversion NA. destruct b; [ eapply IHq2 | eapply IHq1 ]; eassumption.

    pattern c', s'. eapply rep_inv.
      eassumption.
      reflexivity.
      intros. rewrite PRE. eapply IHq. inversion NA. assumption. eassumption.
Qed.

Theorem noassign_prog_same:
  forall v p (NA: prog_noassign v p),
  forall_endstates p (fun _ s _ s' => s v = s' v).
Proof.
  unfold forall_endstates. intros.
  change s' with (snd (x',s')). set (xs':=(x',s')) in *. clearbody xs'.
  pattern xs'. eapply Forall_inv. eapply prog_inv_universal.
    exact XP.
    simpl. rewrite ENTRY. reflexivity.
    intros. apply (noassign_stmt_same v) in XS.
      rewrite PRE. simpl. inversion XS. unfold reset_temps, reset_vars. destruct (archtyps v).
        assumption.
        reflexivity.
      specialize (NA s1 a1). rewrite IL in NA. exact NA.
Qed.

End FrameTheorems.

(* Prove a goal of the form (prog_noassign v p) for a program p that contains no
   statements having assignments to v. *)
Ltac prove_noassign :=
  try lazymatch goal with [ |- prog_noassign _ _ ] => let a := fresh "a" in
    let s := fresh "s" in let a := fresh "a" in intros s a; destruct a as [|a];
    repeat first [ exact I | destruct a as [a|a|] ]
  end;
  repeat lazymatch goal with [ |- _ <> _ ] => discriminate 1
                           | _ => constructor; let g:=numgoals in guard g<=2 end.

End PICINAE_THEORY.


Module PicinaeTheory (IL: PICINAE_IL) <: PICINAE_THEORY IL.
  Include PICINAE_THEORY IL.
End PicinaeTheory.
