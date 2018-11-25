(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Static Semantics Theory module:                     MMMMMMMMMMMMMMMMM^NZMMN+Z
   * boundedness of modular arithmetic outputs,         MMMMMMMMMMMMMMM/.$MZM8O+
   * type-preservation of operational semantics,         MMMMMMMMMMMMMM7..$MNDM+
   * progress of memory-safe programs, and                MMDMMMMMMMMMZ7..$DM$77
   * proof of type-safety.                                 MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
   To compile this module, first load and compile:           MMMMMMMMMM$.$MOMO=7
   * Picinae_core                                             MDMMMMMMMO.7MDM7M+
   * Picinae_theory                                            ZMMMMMMMM.$MM8$MN
   Then compile this module with menu option                   $ZMMMMMMZ..MMMOMZ
   Compile->Compile_buffer.                                     ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_theory.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import FunctionalExtensionality.



(* An IL expression type is a number of bitwidth w, or a memory state with
   addresses of bitwidth w.  (The bitwidth of memory contents is specified
   by the architecture, not the type.) *)
Inductive typ : Type :=
| NumT (w:bitwidth)
| MemT (w:bitwidth).

(* Create an effective decision procedure for type-equality. *)
Theorem typ_eqdec: forall (t1 t2:typ), {t1=t2}+{t1<>t2}.
Proof. decide equality; apply N.eq_dec. Defined.
Arguments typ_eqdec t1 t2 : simpl never.
Instance TypEqDec : EqDec typ := { iseq := typ_eqdec }.

(* The bitwidth of the result of a binary operation *)
Definition widthof_binop (bop:binop_typ) (w:bitwidth) : bitwidth :=
  match bop with
  | OP_PLUS | OP_MINUS | OP_TIMES | OP_DIVIDE | OP_SDIVIDE | OP_MOD | OP_SMOD
  | OP_LSHIFT | OP_RSHIFT | OP_ARSHIFT | OP_AND | OP_OR | OP_XOR => w
  | OP_EQ | OP_NEQ | OP_LT | OP_LE | OP_SLT | OP_SLE => 1
  end.


Section OpBounds.

(* Establish upper bounds on various arithmetic and logical operations. *)

Remark Nlt_0_pow2: forall p, 0 < 2^p.
Proof. intros. apply N.neq_0_lt_0, N.pow_nonzero. discriminate 1. Qed.

Remark Zlt_0_pow2: forall p, (0 < Z.of_N (2^p))%Z.
Proof. intro. rewrite <- N2Z.inj_0. apply N2Z.inj_lt. apply Nlt_0_pow2. Qed.

Lemma div_bound: forall n1 n2, N.div n1 n2 <= n1.
Proof.
  intros.
  destruct n2. destruct n1. reflexivity. apply N.le_0_l.
  apply N.div_le_upper_bound. discriminate 1.
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
  intros. destruct w as [|w]. unfold signed_range in RX,RY. subst. reflexivity.
  destruct y as [|p2|p2]; destruct x as [|p1|p1]; try assumption;
  specialize (BP p1 p2); destruct BP as [BP1 BP2].

  (* x>0, y>0 *)
  unfold signed_range. split.
    transitivity Z0. apply Z.opp_nonpos_nonneg. rewrite <- N2Z.inj_0. apply N2Z.inj_le. apply N.le_0_l. assumption.
    transitivity (Z.pos p2). assumption. apply (proj2 RY).

  (* x<0, y>0 *)
  rewrite <- Pos2Z.opp_pos, Z.rem_opp_l; [|discriminate]. split.
    apply -> Z.opp_le_mono. apply Z.lt_le_incl. transitivity (Z.pos p2). assumption. apply (proj2 RY).
    apply Z.le_lt_trans with (m:=Z0). apply Z.opp_nonpos_nonneg. assumption. apply Zlt_0_pow2.

  (* x>0, y<0 *)
  rewrite <- Pos2Z.opp_pos, Z.rem_opp_r; [|discriminate]. split.
    transitivity Z0. apply Z.opp_nonpos_nonneg. rewrite <- N2Z.inj_0. apply N2Z.inj_le. apply N.le_0_l. assumption.
    apply Z.lt_le_trans with (m:=Z.pos p2).
      assumption.
      apply proj1 in RY. rewrite <- Pos2Z.opp_pos in RY. apply Z.opp_le_mono in RY. assumption.

  (* x<0, y<0 *)
  do 2 rewrite <- Pos2Z.opp_pos. rewrite Z.rem_opp_r,Z.rem_opp_l; try discriminate. split.
    apply -> Z.opp_le_mono. transitivity (Z.pos p1).
      apply Z.rem_le. apply Pos2Z.is_nonneg. apply Pos2Z.is_pos.
      apply proj1 in RX. rewrite <- Pos2Z.opp_pos in RX. apply Z.opp_le_mono. assumption.
    apply Z.le_lt_trans with (m:=Z0). apply Z.opp_nonpos_nonneg. assumption. apply Zlt_0_pow2.
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
    apply Nlt_0_pow2.
    assumption.
Qed.

Lemma shiftr_bound:
  forall w x y, x < 2^w -> N.shiftr x y < 2^(w-y).
Proof.
  intros. destruct (N.le_gt_cases y w).
    rewrite N.shiftr_div_pow2. apply N.div_lt_upper_bound.
      apply N.pow_nonzero. discriminate 1.
      rewrite <- N.pow_add_r, N.add_sub_assoc, N.add_comm, N.add_sub; assumption.
    destruct x as [|x]. 
      rewrite N.shiftr_0_l. apply Nlt_0_pow2.
      rewrite N.shiftr_eq_0. apply Nlt_0_pow2. apply N.log2_lt_pow2.
        reflexivity.
        etransitivity. eassumption. apply N.pow_lt_mono_r. reflexivity. assumption.
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
  forall w x y, x < 2^w -> y < 2^w -> N.land x y < 2^w.
Proof.
  intros. apply logic_op_bound; try assumption.
  intros. rewrite N.land_spec, Z1, Z2. reflexivity.
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


Section HasUpperBound.

(* Define the has-upper-bound property of pairs of partial functions, and
   prove some general sufficiency conditions for having the property. *)

Definition has_upper_bound {A B} (f g: A -> option B) :=
  forall x y z, f x = Some y -> g x = Some z -> y = z.

Lemma hub_refl:
  forall A B (f: A -> option B), has_upper_bound f f.
Proof.
  unfold has_upper_bound. intros.
  rewrite H0 in H. inversion H.
  reflexivity.
Qed.

Lemma hub_subset:
  forall A B (f g f' g': A -> option B) (HUB: has_upper_bound f g)
         (SS1: f' ⊆ f) (SS2: g' ⊆ g),
  has_upper_bound f' g'.
Proof.
  unfold has_upper_bound. intros. eapply HUB.
    apply SS1. eassumption.
    apply SS2. assumption.
Qed.

Lemma hub_update {A B} {eq:EqDec A}:
  forall (f g: A -> option B) x y (HUB: has_upper_bound f g),
  has_upper_bound (f[x:=y]) (g[x:=y]).
Proof.
  unfold has_upper_bound. intros. destruct (x0 == x).
    subst. rewrite update_updated in H,H0. rewrite H0 in H. inversion H. reflexivity.
    rewrite update_frame in H,H0 by assumption. eapply HUB; eassumption.
Qed.

End HasUpperBound.



Module Type PICINAE_STATICS (IL: PICINAE_IL).

(* This module proves that the semantics of the IL are type-safe in the sense that
   programs whose constants have proper bitwidths never produce variable values or
   expressions that exceed their declared bitwidths as they execute.  This is
   important for (1) providing assurance that the semantics are correctly defined,
   and (2) proving practical results that rely upon the assumption that machine
   registers and memory contents always have values of appropriate bitwidths. *)

Import IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.
Open Scope N.

(* Memory is well-typed if every address holds a byte. *)
Definition welltyped_memory (m:addr->N) : Prop :=
  forall a, m a < 2^Mb.

(* A constant's type is its bitwidth, and a memory's type is the
   bitwidth of its addresses. *)
Inductive hastyp_val: value -> typ -> Prop :=
| TVN (n:N) (w:bitwidth) (LT: n < 2^w): hastyp_val (VaN n w) (NumT w)
| TVM (m:addr->N) (w:bitwidth) (WTM: welltyped_memory m): hastyp_val (VaM m w) (MemT w).

(* A typing context is a partial map from variables to types. *)
Definition typctx := var -> option typ.

(* Type-check an expression in a typing context, returning its type. *)
Inductive hastyp_exp (c:typctx): exp -> typ -> Prop :=
| TVar v t (CV: c v = Some t): hastyp_exp c (Var v) t
| TWord n w (LT: n < 2^w): hastyp_exp c (Word n w) (NumT w)
| TLoad e1 e2 en len mw
        (T1: hastyp_exp c e1 (MemT mw)) (T2: hastyp_exp c e2 (NumT mw)):
        hastyp_exp c (Load e1 e2 en len) (NumT (Mb*len))
| TStore e1 e2 e3 en len mw
         (T1: hastyp_exp c e1 (MemT mw)) (T2: hastyp_exp c e2 (NumT mw))
         (T3: hastyp_exp c e3 (NumT (Mb*len))):
         hastyp_exp c (Store e1 e2 e3 en len) (MemT mw)
| TBinOp bop e1 e2 w
         (T1: hastyp_exp c e1 (NumT w)) (T2: hastyp_exp c e2 (NumT w)):
         hastyp_exp c (BinOp bop e1 e2) (NumT (widthof_binop bop w))
| TUnOp uop e w (T1: hastyp_exp c e (NumT w)):
        hastyp_exp c (UnOp uop e) (NumT w)
| TCast ct w w' e (T1: hastyp_exp c e (NumT w))
        (LE: match ct with CAST_UNSIGNED | CAST_SIGNED => w <= w'
                         | CAST_HIGH | CAST_LOW => w' <= w end):
        hastyp_exp c (Cast ct w' e) (NumT w')
| TLet v e1 e2 t1 t2
       (T1: hastyp_exp c e1 t1) (T2: hastyp_exp (c[v:=Some t1]) e2 t2):
       hastyp_exp c (Let v e1 e2) t2
| TUnknown w: hastyp_exp c (Unknown w) (NumT w)
| TIte e1 e2 e3 w t
       (T1: hastyp_exp c e1 (NumT w)) (T2: hastyp_exp c e2 t) (T3: hastyp_exp c e3 t):
       hastyp_exp c (Ite e1 e2 e3) t
| TExtract w n1 n2 e1
           (T1: hastyp_exp c e1 (NumT w)) (LO: n2 <= n1) (HI: n1 < w):
           hastyp_exp c (Extract n1 n2 e1) (NumT (N.succ (n1-n2)))
| TConcat e1 e2 w1 w2
          (T1: hastyp_exp c e1 (NumT w1)) (T2: hastyp_exp c e2 (NumT w2)):
          hastyp_exp c (Concat e1 e2) (NumT (w1+w2)).

(* Static semantics for statements:
   Defining a sound statement typing semantics is tricky for two reasons:

   (1) There are really two kinds of IL variables: (a) those that encode cpu state
   (which are always initialized, and whose types are fixed), and (b) temporary
   variables introduced during lifting to IL (which are not guaranteed to be
   initialized, and whose types may vary across different instruction IL blocks.

   We therefore use separate contexts c0 and c to model the two kinds.  Context
   c0 models the cpu state variables, while c models all variables.  Context c
   therefore usually subsumes c0, and is always consistent with c0 (i.e., the
   join of c and c0 is always a valid context).  This consistency is enforced
   by checking assigned value types against c0 at every Move, but only updating c.

   (2) Since variable initialization states are mutable, we need static rules
   that support meets and joins of contexts.  But a general weakening rule is
   inconveniently broad; it hampers syntax-directed inductive proofs, since it
   is potentially applicable to all statement forms during inversions.

   To avoid this, we instead define a strategically chosen weakening clause
   within the sequence typing rule (TSeq), along with a fixed point requirement
   for loops (TRep).  An IL program that only assigns values of one type to
   each variable per instruction encoding can be safely type-checked by ignoring
   both clauses; the fixed point condition is automatically satisfied if the
   weakening clause is never utilized.  But including these two clauses yields
   a provably type-safe semantics because the weakening clause adds just enough
   flexibility to prove satisfaction of the fixed point requirement without
   having to cope with a fully generalized weakening rule. *)

Inductive hastyp_stmt (c0 c:typctx): stmt -> typctx -> Prop :=
| TNop: hastyp_stmt c0 c Nop c
| TMove v t e (CV: c0 v = None \/ c0 v = Some t) (TE: hastyp_exp c e t):
    hastyp_stmt c0 c (Move v e) (c[v:=Some t])
| TJmp e w (TE: hastyp_exp c e (NumT w)): hastyp_stmt c0 c (Jmp e) c
| TExn ex: hastyp_stmt c0 c (Exn ex) c
| TSeq q1 q2 c1 c2 c' (SS: c2 ⊆ c1)
       (TS1: hastyp_stmt c0 c q1 c1) (TS2: hastyp_stmt c0 c2 q2 c'):
    hastyp_stmt c0 c (Seq q1 q2) c'
| TIf e q1 q2 c1 c2 c' (SS1: c' ⊆ c1) (SS2: c' ⊆ c2)
      (TE: hastyp_exp c e (NumT 1))
      (TS1: hastyp_stmt c0 c q1 c1) (TS2: hastyp_stmt c0 c q2 c2):
    hastyp_stmt c0 c (If e q1 q2) c'
| TRep e w q c' (SS: c ⊆ c')
    (TE: hastyp_exp c e (NumT w)) (TS: hastyp_stmt c0 c q c'):
    hastyp_stmt c0 c (Rep e q) c.

(* A program is well-typed if all its statements are well-typed. *)
Definition welltyped_prog (c0:typctx) (p:program) : Prop :=
  forall s a, match p s a with None => True | Some (_,q) =>
                exists c', hastyp_stmt c0 c0 q c' end.


(* Convenience lemmas for inverted reasoning about hastyp_val. *)

Lemma value_bound:
  forall n w (TV: hastyp_val (VaN n w) (NumT w)), n < 2^w.
Proof. intros. inversion TV. assumption. Qed.

Lemma mem_welltyped:
  forall m w (TV: hastyp_val (VaM m w) (MemT w)), welltyped_memory m.
Proof. intros. inversion TV. assumption. Qed.

Lemma hastyp_towidth:
  forall w n, hastyp_val (towidth w n) (NumT w).
Proof.
  intros. apply TVN.
  apply N.mod_upper_bound.
  apply N.pow_nonzero.
  intro. discriminate.
Qed.


(* These short lemmas are helpful when automating type-checking in tactics. *)
Lemma hastyp_binop:
  forall bop c e1 e2 w w' (W: widthof_binop bop w = w')
         (T1: hastyp_exp c e1 (NumT w)) (T2: hastyp_exp c e2 (NumT w)),
  hastyp_exp c (BinOp bop e1 e2) (NumT w').
Proof.
  intros. rewrite <- W. apply TBinOp; assumption.
Qed.

Lemma hastyp_extract:
  forall w c n1 n2 e1 w' (W: N.succ (n1-n2) = w')
         (T1: hastyp_exp c e1 (NumT w)) (LO: n2 <= n1) (HI: n1 < w),
  hastyp_exp c (Extract n1 n2 e1) (NumT w').
Proof.
  intros. rewrite <- W. apply TExtract with (w:=w); assumption.
Qed.

Lemma hastyp_concat:
  forall c e1 e2 w1 w2 w' (W: w1+w2 = w')
         (T1: hastyp_exp c e1 (NumT w1)) (T2: hastyp_exp c e2 (NumT w2)),
  hastyp_exp c (Concat e1 e2) (NumT w').
Proof.
  intros. rewrite <- W. apply TConcat; assumption.
Qed.


(* Expression types are unique. *)
Theorem hastyp_exp_unique:
  forall e c1 c2 t1 t2 (HUB: has_upper_bound c1 c2)
         (TE1: hastyp_exp c1 e t1) (TE2: hastyp_exp c2 e t2),
  t1 = t2.
Proof.
  intros. revert c1 c2 t1 t2 HUB TE1 TE2. induction e; intros;
  inversion TE1; inversion TE2; clear TE1 TE2; subst;
  try reflexivity.

  (* Var *)
  eapply HUB; eassumption.

  (* Store *)
  eapply IHe1; eassumption.

  (* BinOp *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). inversion IHe1. reflexivity.

  (* UnOp *)
  specialize (IHe _ _ _ _ HUB T1 T0). inversion IHe. reflexivity.

  (* Let *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). subst.
  refine (IHe2 _ _ _ _ _ T2 T3). apply hub_update. exact HUB.

  (* Extract *)
  exact (IHe2 _ _ _ _ HUB T2 T4).

  (* Concat *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). inversion IHe1. subst.
  specialize (IHe2 _ _ _ _ HUB T2 T3). inversion IHe2. subst.
  reflexivity.
Qed.

(* Statement types are compatible (though not necessarily unique). *)
Theorem hastyp_stmt_compat:
  forall c0 q c1 c2 c1' c2'
         (HUB: has_upper_bound c1 c2)
         (TS1: hastyp_stmt c0 c1 q c1') (TS2: hastyp_stmt c0 c2 q c2'),
  has_upper_bound c1' c2'.
Proof.
  induction q; intros; inversion TS1; inversion TS2; clear TS1 TS2; subst;
  try exact HUB.

  (* Move *)
  replace t0 with t in * by (eapply hastyp_exp_unique; eassumption).
  apply hub_update. exact HUB.

  (* Seq *)
  eapply IHq2; [|eassumption..].
  eapply hub_subset; [|eassumption..].
  eapply IHq1; eassumption.

  (* If *)
  clear SS2 SS3. eapply hub_subset; [|eassumption..].
  eapply IHq1; eassumption.
Qed.

(* Expression typing contexts can be safely weakened. *)
Theorem hastyp_exp_weaken:
  forall c1 c2 e t (TE: hastyp_exp c1 e t) (SS: c1 ⊆ c2),
  hastyp_exp c2 e t.
Proof.
  intros. revert c2 SS. dependent induction TE; intros; econstructor;
  try (try first [ apply IHTE | apply IHTE1 | apply IHTE2 | apply IHTE3 | apply SS ]; assumption).

  apply IHTE2. unfold update. intros v0 t CV. destruct (v0 == v).
    assumption.
    apply SS. assumption.
Qed.

(* Statement frame contexts can be safely weakened. *)
Theorem hastyp_stmt_weaken:
  forall c0 c0' q c c' (TS: hastyp_stmt c0 c q c') (SS: c0' ⊆ c0),
  hastyp_stmt c0' c q c'.
Proof.
  induction q; intros; inversion TS; subst.
    apply TNop.
    apply TMove.
      specialize (SS v). destruct (c0' v).
        right. rewrite (SS t0 (eq_refl _)) in CV. destruct CV. discriminate. assumption.
        left. reflexivity.
      exact TE.
    eapply TJmp. exact TE.
    apply TExn.
    eapply TSeq. exact SS0.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
    eapply TIf. exact SS1. exact SS2.
      exact TE.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
    eapply TRep. exact SS0.
      exact TE.
      apply IHq. exact TS0. exact SS.
Qed.


(* We next prove type-safety of the IL with respect to the above static semantics.
   In general, interpretation of an arbitrary, unchecked IL program can fail
   (i.e., exec_prog is underivable) for only the following reasons:

   (1) memory access violation ("mem_readable" or "mem_writable" is falsified), or

   (2) a type-mismatch occurs (e.g., addition applied to memory stores).

   Type-safety proves that if type-checking succeeds, then the only reachable
   stuck-states are case (1).  That is, runtime type-mismatches are precluded,
   and all computed values have proper types.

   This property is important in the context of formal validation of native
   code programs because proofs about such code typically rely upon the types
   of values that each cpu state element can hold (e.g., 32-bit registers always
   contain 32-bit numbers).  Proving type-safety allows us to verify these
   basic properties within other proofs by first running the type-checker (as a
   tactic), and then applying the type-soundness theorem(s). *)


(* Binary operations on well-typed values yield well-typed values. *)
Theorem typesafe_binop:
  forall bop n1 n2 w
         (TV1: hastyp_val (VaN n1 w) (NumT w)) (TV2: hastyp_val (VaN n2 w) (NumT w)),
  hastyp_val (eval_binop bop w n1 n2) (NumT (widthof_binop bop w)).
Proof.
  intros. destruct bop; try first [ apply hastyp_towidth | apply TVN, bit_bound ];
  apply TVN; try apply ofZ_bound.

  (* DIV *)
  eapply N.le_lt_trans. apply div_bound. apply value_bound. assumption.

  (* SMOD *)
  apply mod_bound; apply value_bound; assumption.

  (* SHIFTR *)
  eapply N.lt_le_trans.
    apply shiftr_bound. apply value_bound. eassumption.
    apply N.pow_le_mono_r. discriminate 1. apply N.le_sub_l.

  (* LAND *)
  apply land_bound; apply value_bound; assumption.

  (* LOR *)
  apply lor_bound; apply value_bound; assumption.

  (* LXOR *)
  apply lxor_bound; apply value_bound; assumption.
Qed.

(* Unary operations on well-typed values yield well-typed values. *)
Theorem typesafe_unop:
  forall uop n w
         (TV: hastyp_val (VaN n w) (NumT w)),
  hastyp_val (eval_unop uop n w) (NumT w).
Proof.
  intros. destruct uop; apply TVN.

  (* NEG *)
  apply N.mod_upper_bound, N.pow_nonzero. discriminate 1.

  (* NOT *)
  apply lnot_bound, value_bound. assumption.
Qed.

(* Casts of well-typed values yield well-typed values. *)
Theorem typesafe_cast:
  forall c n w w' (TV: hastyp_val (VaN n w) (NumT w))
    (T: match c with CAST_UNSIGNED | CAST_SIGNED => w<=w'
                   | CAST_HIGH | CAST_LOW => w'<=w end),
  hastyp_val (VaN (cast c w w' n) w') (NumT w').
Proof.
  intros. inversion TV. subst. destruct c; simpl.

  (* LOW *)
  apply hastyp_towidth.

  (* HIGH *)
  apply TVN, cast_high_bound; assumption.

  (* SIGNED *)
  apply TVN, ofZ_bound.

  (* UNSIGNED *)
  apply TVN. eapply N.lt_le_trans. eassumption.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

(* Memory-loads of well-typed arguments yield well-typed results. *)
Theorem getmem_bound:
  forall e len m a (WTM: welltyped_memory m),
  getmem e len m a < 2^(Mb*len).
Proof.
  intros. revert a. induction len using N.peano_ind; intro.
    rewrite N.mul_0_r. apply Nlt_0_pow2.
    rewrite getmem_succ. destruct e; apply lor_bound.
      eapply N.lt_le_trans.
        apply IHlen.
        apply N.pow_le_mono_r. discriminate 1. apply N.mul_le_mono_nonneg_l. apply N.le_0_l. apply N.le_succ_diag_r.
      rewrite N.shiftl_mul_pow2, N.mul_succ_r, N.add_comm, N.pow_add_r. apply N.mul_lt_mono_pos_r.
        apply Nlt_0_pow2.
        apply WTM.
      eapply N.lt_le_trans.
        apply WTM.
        apply N.pow_le_mono_r. discriminate 1. rewrite N.mul_succ_r, N.add_comm. apply N.le_add_r.
      rewrite N.shiftl_mul_pow2, N.mul_succ_r, N.pow_add_r. apply N.mul_lt_mono_pos_r.
        apply Nlt_0_pow2.
        apply IHlen.
Qed.

Theorem typesafe_getmem:
  forall mw len m a e (TV: hastyp_val (VaM m mw) (MemT mw)),
  hastyp_val (VaN (getmem e len m a) (Mb*len)) (NumT (Mb*len)).
Proof.
  intros. apply TVN. apply getmem_bound. eapply mem_welltyped. eassumption.
Qed.

(* Stores into well-typed memory yield well-typed memory. *)
Theorem setmem_welltyped:
  forall e len m a v (WTM: welltyped_memory m) (VM: v < 2^(Mb*len)),
  welltyped_memory (setmem e len m a v).
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. apply WTM.
    rewrite setmem_succ. destruct e; (apply IHlen; [intro a'; destruct (N.eq_dec a' a); [subst a'|]|]).
      rewrite update_updated, N.shiftr_div_pow2. apply N.div_lt_upper_bound.
        apply N.pow_nonzero. discriminate 1.
        rewrite <- N.pow_add_r, <- N.mul_succ_r. exact VM.
      rewrite update_frame by assumption. apply WTM.
      apply N.mod_lt, N.pow_nonzero. discriminate 1.
      rewrite update_updated. destruct len.
        eapply N.lt_le_trans. exact VM. rewrite N.mul_1_r. reflexivity.
        apply N.mod_lt, N.pow_nonzero. discriminate 1.
      rewrite update_frame by assumption. apply WTM.
      rewrite N.shiftr_div_pow2. apply N.div_lt_upper_bound.
        apply N.pow_nonzero. discriminate 1.
        rewrite <- N.pow_add_r, N.add_comm, <- N.mul_succ_r. exact VM.
Qed.

Corollary typesafe_setmem:
  forall len mw m a v e
         (TV1: hastyp_val (VaM m mw) (MemT mw))
         (TV3: hastyp_val (VaN v (Mb*len)) (NumT (Mb*len))),
  hastyp_val (VaM (setmem e len m a v) mw) (MemT mw).
Proof.
  intros. apply TVM, setmem_welltyped.
    eapply mem_welltyped. eassumption.
    apply value_bound. assumption.
Qed.


(* Context c "models" a store s if all variables in c have values in s
   that are well-typed with respect to c. *)
Definition models (c:typctx) (s:store) : Prop :=
  forall v t (CV: c v = Some t),
  exists u, s v = Some u /\ hastyp_val u t.

(* Values read from well-typed memory and registers have appropriate bitwidth. *)
Theorem models_wtm:
  forall {c s v mem mw} (MDL: models c s) (MEM: s v = Some (VaM mem mw)),
  match c v with Some _ => welltyped_memory mem | None => True end.
Proof.
  intros. specialize (MDL v). destruct (c v); [|exact I].
  destruct (MDL t (eq_refl _)) as [x [H1 H2]].
  rewrite H1 in MEM. injection MEM as. subst x.
  inversion H2. assumption.
Qed.

Theorem models_regsize:
  forall {c s v u w} (MDL: models c s) (VAL: s v = Some (VaN u w)),
  match c v with Some _ => u < 2^w | None => True end.
Proof.
  intros. specialize (MDL v). destruct (c v); [|exact I].
  destruct (MDL t (eq_refl _)) as [x [H1 H2]].
  rewrite H1 in VAL. injection VAL as. subst x.
  inversion H2. assumption.
Qed.

(* Shrinking the typing context preserves the modeling relation. *)
Lemma models_subset:
  forall c s c' (M: models c s) (SS: c' ⊆ c),
  models c' s.
Proof.
  unfold models. intros.
  apply SS in CV. apply M in CV. destruct CV as [u [SV T]].
  exists u. split; assumption.
Qed.

(* Every result of evaluating a well-typed expression is a well-typed value. *)
Lemma preservation_eval_exp:
  forall {h s e c t u}
         (MCS: models c s) (TE: hastyp_exp c e t) (E: eval_exp h s e u),
  hastyp_val u t.
Proof.
  intros. revert s u MCS E. dependent induction TE; intros;
  inversion E; subst;
  repeat (match goal with [ IH: forall _ _, models _ _ -> eval_exp ?h _ ?e _ -> hastyp_val _ _,
                            M: models _ ?s,
                            EE: eval_exp ?h ?s ?e _ |- _ ] =>
            specialize (IH s _ MCS EE); try (inversion IH; [idtac]; subst) end).

  (* Var *)
  apply MCS in CV. destruct CV as [u' [SID TVU]].
  rewrite SID in SV. injection SV. intro. subst.
  assumption.

  (* Word *)
  apply TVN. assumption.

  (* Load *)
  eapply typesafe_getmem; eassumption.

  (* Store *)
  apply typesafe_setmem; assumption.

  (* BinOp *)
  apply typesafe_binop; assumption.

  (* UnOp *)
  apply typesafe_unop; assumption.

  (* Cast *)
  apply typesafe_cast; assumption.

  (* Let *)
  assert (CS': models (c[v:=Some t1]) (s[v:=Some u1])).
    unfold update. intros v0 t0 VEQT. destruct (v0 == v).
      exists u1. split. reflexivity. injection VEQT. intro. subst t0. assumption.
      apply MCS in VEQT. assumption.
  revert CS' E2. apply IHTE2.

  (* Unknown *)
  apply TVN. assumption.

  (* Ite *)
  destruct n1.
    revert MCS E'. apply IHTE3.
    revert MCS E'. apply IHTE2.

  (* Extract *)
  apply typesafe_cast.
    apply typesafe_cast. assumption. apply N.le_succ_l. assumption.
    apply -> N.succ_le_mono. apply N.le_sub_l.

  (* Concat *)
  apply TVN. apply concat_bound; assumption.
Qed.


(* If an expression is well-typed and there are no memory access violations,
   then evaluating it always succeeds (never gets "stuck"). *)

Lemma progress_eval_exp:
  forall {s e c t}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_exp c e t),
  exists u, eval_exp htotal s e u.
Proof.
  intros. revert s MCS. dependent induction T; intros;
  repeat match reverse goal with [ IH: forall _, models ?C _ -> exists _, eval_exp _ _ ?e _,
                                    M: models ?c ?s,
                                    T: hastyp_exp ?c ?e _ |- _ ] =>
    specialize (IH s M);
    let u':=fresh "u" in let EE:=fresh "E" in let TV:=fresh "TV" in
      destruct IH as [u' EE];
      assert (TV:=preservation_eval_exp M T EE);
      try (inversion TV; [idtac]; subst)
  end.

  (* Var *)
  apply MCS in CV. destruct CV as [u [SV TV]].
  exists u. apply EVar; assumption.

  (* Word *)
  exists (VaN n w). apply EWord; assumption.

  (* Load *)
  eexists. eapply ELoad; try eassumption. intros. split. reflexivity. apply RW.

  (* Store *)
  eexists. eapply EStore; try eassumption. intros. split. reflexivity. apply RW.

  (* BinOp *)
  eexists. apply EBinOp; eassumption.

  (* UnOp *)
  eexists. apply EUnOp; eassumption.

  (* Cast *)
  eexists. apply ECast; eassumption.

  (* Let *)
  assert (CS': models (c[v:=Some t1]) (s[v:=Some u])).
    unfold update. intros v0 t0 VEQT. destruct (v0 == v).
      exists u. split. reflexivity. injection VEQT. intro. subst t0. assumption.
      apply MCS in VEQT. assumption.
  edestruct IHT2 as [u2 EE2].
    apply CS'.
    exists u2. eapply ELet; eassumption.

  (* Unknown *)
  exists (VaN 0 w). apply EUnknown. apply Nlt_0_pow2.

  (* Ite *)
  eexists (match n with N0 => u0 | _ => u end).
  apply EIte with (n1:=n) (w1:=w). assumption. destruct n; assumption.

  (* Extract *)
  eexists. apply EExtract; eassumption.

  (* Concat *)
  eexists. apply EConcat; eassumption.
Qed.

Remark welltyped_rep:
  forall e c0 c q n (TS: hastyp_stmt c0 c (Rep e q) c),
  hastyp_stmt c0 c (N.iter n (Seq q) Nop) c.
Proof.
  intros. inversion TS; subst. apply Niter_invariant.
    apply TNop.
    intros. eapply TSeq; eassumption.
Qed.

(* Statement execution preserves the modeling relation. *)
Lemma preservation_exec_stmt:
  forall {h s q c0 c c' s'}
         (MCS: models c s) (T: hastyp_stmt c0 c q c') (XS: exec_stmt h s q s' None),
  models c' s'.
Proof.
  intros. revert c c' MCS T. dependent induction XS; intros; inversion T; subst;
  try assumption.

  unfold update. intros v0 t0 T0. destruct (v0 == v).
    subst. injection T0; intro; subst. exists u. split. reflexivity. apply (preservation_eval_exp MCS TE E).
    apply MCS; assumption.

  apply IHXS2 with (c:=c2).
    reflexivity.
    apply models_subset with (c:=c1).
      apply IHXS1 with (c:=c). reflexivity. assumption. assumption.
      assumption.
    assumption.

  destruct c.
    apply models_subset with (c:=c3).
      apply IHXS with (c:=c1). reflexivity. assumption. assumption.
      assumption.
    apply models_subset with (c:=c2).
      apply IHXS with (c:=c1). reflexivity. assumption. assumption.
      assumption.

  apply IHXS with (c:=c') (c':=c').
    reflexivity.
    assumption.

  eapply welltyped_rep; eassumption.
Qed.

(* Execution also preserves modeling the frame context c0. *)
Lemma pres_frame_exec_stmt:
  forall {h s q c0 c c' s' x} (MC0S: models c0 s) (MCS: models c s)
         (T: hastyp_stmt c0 c q c') (XS: exec_stmt h s q s' x),
  models c0 s'.
Proof.
  intros. revert c c' MCS T. dependent induction XS; intros;
  try assumption;
  inversion T; subst.

  intros v0 t0 CV0. unfold update. destruct (v0 == v).
    subst. exists u. split. reflexivity. destruct CV as [CV|CV]; rewrite CV0 in CV.
      discriminate.
      injection CV. intro. subst t0. apply (preservation_eval_exp MCS TE E).
    apply MC0S in CV0. destruct CV0 as [u0 [SV0 TV0]]. exists u0. split; assumption.

  apply IHXS with (c:=c) (c':=c1); assumption.

  apply IHXS2 with (c:=c2) (c':=c').
    apply IHXS1 with (c:=c) (c':=c1); assumption.
    apply models_subset with (c:=c1).
      apply (preservation_exec_stmt MCS TS1 XS1).
      assumption.
    assumption.

  destruct c.
    apply IHXS with (c:=c1) (c':=c3); assumption.
    apply IHXS with (c:=c1) (c':=c2); assumption.

  apply IHXS with (c:=c') (c':=c'); try assumption.
  eapply welltyped_rep; eassumption.
Qed.

(* Well-typed statements never get "stuck" except for memory access violations.
   They either exit or run to completion. *)
Lemma progress_exec_stmt:
  forall {s q c0 c c'}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_stmt c0 c q c'),
  exists s' x, exec_stmt htotal s q s' x.
Proof.
  intros. revert c c' s T MCS. induction q using stmt_ind2; intros;
  try (inversion T; subst).

  (* Nop *)
  exists s,None. apply XNop.

  (* Move *)
  destruct (progress_eval_exp RW MCS TE) as [u E].
  exists (s[v:=Some u]),None. apply XMove. assumption.

  (* Jmp *)
  destruct (progress_eval_exp RW MCS TE) as [u E].
  assert (TV:=preservation_eval_exp MCS TE E). inversion TV as [a' w'|]; subst.
  exists s,(Some (Exit a')). apply XJmp with (w:=w). assumption.

  (* Exn *)
  exists s,(Some (Raise i)). apply XExn.

  (* Seq *)
  destruct (IHq1 _ _ _ TS1 MCS) as [s2 [x2 XS1]]. destruct x2.
    exists s2,(Some e). apply XSeq1. exact XS1.
    destruct (IHq2 _ _ s2 TS2) as [s' [x' XS2]].
      eapply models_subset.
        eapply preservation_exec_stmt; eassumption.
        exact SS.
      exists s',x'. eapply XSeq2; eassumption.

  (* If *)
  destruct (progress_eval_exp RW MCS TE) as [u E].
  assert (TV:=preservation_eval_exp MCS TE E). inversion TV as [cnd w|]; subst.
  destruct cnd as [|cnd].
    destruct (IHq2 _ _ _ TS2 MCS) as [s'2 [x2 XS2]]. exists s'2,x2. apply XIf with (c:=0); assumption.
    destruct (IHq1 _ _ _ TS1 MCS) as [s'1 [x1 XS1]]. exists s'1,x1. apply XIf with (c:=N.pos cnd); assumption.

  (* Rep *)
  destruct (progress_eval_exp RW MCS TE) as [u E].
  assert (TV:=preservation_eval_exp MCS TE E). inversion TV; subst.
  destruct (IHq2 n c' c' s) as [s' [x XS]].
    apply Niter_invariant.
      apply TNop.
      intros. eapply TSeq; eassumption.
    exact MCS.
    exists s',x. eapply XRep. exact E. assumption.
Qed.

(* Well-typed programs preserve the modeling relation at every execution step. *)
Theorem preservation_exec_prog:
  forall h p c s n a s' x (MCS: models c s)
         (WP: welltyped_prog c p) (XS: exec_prog h p a s n s' x),
  models c s'.
Proof.
  intros. revert a s x MCS XS. induction n; intros; inversion XS; clear XS; subst.
    assumption.
    eapply IHn.
      specialize (WP s a). rewrite LU in WP. destruct WP as [c' TS]. eapply pres_frame_exec_stmt.
        exact MCS. exact MCS. exact TS. exact XS0.
      exact XP.
    specialize (WP s a). rewrite LU in WP. destruct WP as [c' TS]. eapply pres_frame_exec_stmt.
      exact MCS. exact MCS. exact TS. exact XS0.
Qed.

(* Well-typed programs never get "stuck" except for memory access violations.
   They exit, or run to completion.  They never get "stuck" due to a runtime
   type-mismatch. *)
Theorem progress_exec_prog:
  forall p c0 s0 n a s1 a'
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c0 s0) (WP: welltyped_prog c0 p)
         (XP: exec_prog htotal p a s0 n s1 (Exit a')) (IL: p s1 a' <> None),
  exists s' x, exec_prog htotal p a s0 (S n) s' x.
Proof.
  intros.
  assert (WPA':=WP s1 a'). destruct (p s1 a') as [(sz,q)|] eqn:IL'; [|contradict IL; reflexivity]. clear IL.
  destruct WPA' as [c' T]. eapply progress_exec_stmt in T.
    destruct T as [s' [x XS]]. exists s'. eapply exec_prog_append in XS; [|exact XP | exact IL'].
      destruct x as [e|]; [destruct e|]; eexists; exact XS.
    exact RW.
    eapply preservation_exec_prog. exact MCS. exact WP. exact XP.
Qed.


(* We next define an effective procedure for type-checking expressions and
   statements.  This procedure is sound but incomplete: it can determine well-
   typedness of most statements, but there exist well-typed statements for
   which it cannot decide their well-typedness.  This happens because the
   formal semantics above allow arbitrary ("magic") context-weakening within
   the rules for Seq, If, and Rep, wherein an effective procedure must guess
   the greatest-lower-bound context sufficient to type-check the remainder of
   the statement.  The procedure below makes the following guesses, which
   suffice to prove well-typedness for IL encodings of all ISAs so far:
     (1) No weakening occurs within Seq.
     (2) If-contexts are weakened to the lattice-meet of the two branches.
     (3) Rep-contexts are weakened to the input context, to get a fixpoint.
   If these guesses cannot typecheck some statements in your ISA, consider
   changing the lifter for your ISA to produce IL encodings whose variable
   types are not path-sensitive. *)

(* Type-check an expression in a given typing context. *)
Fixpoint typchk_exp (e:exp) (c:typctx): option typ :=
  match e with
  | Var v => c v
  | Word n w => if n <? 2^w then Some (NumT w) else None
  | Load e1 e2 _ len =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some (MemT w1), Some (NumT w2) => if w1 =? w2 then Some (NumT (Mb*len)) else None
      | _, _ => None
      end
  | Store e1 e2 e3 _ len =>
      match typchk_exp e1 c, typchk_exp e2 c, typchk_exp e3 c with
      | Some (MemT w1), Some (NumT w2), Some (NumT w) =>
          if andb (w1 =? w2) (w =? Mb*len) then Some (MemT w1) else None
      | _, _, _ => None
      end
  | BinOp bop e1 e2 =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some (NumT w1), Some (NumT w2) =>
          if w1 =? w2 then Some (NumT (widthof_binop bop w1)) else None
      | _, _ => None
      end
  | UnOp uop e1 => match typchk_exp e1 c with Some (NumT w) => Some (NumT w)
                                            | _ => None end
  | Cast ct w' e1 =>
      match typchk_exp e1 c with Some (NumT w) => 
        if match ct with CAST_UNSIGNED | CAST_SIGNED => w <=? w'
                       | CAST_HIGH | CAST_LOW => w' <=? w end then Some (NumT w') else None
      | _ => None
      end
  | Let v e1 e2 =>
      match typchk_exp e1 c with Some t => typchk_exp e2 (c[v:=Some t])
                               | None => None end
  | Unknown w => Some (NumT w)
  | Ite e1 e2 e3 =>
      match typchk_exp e1 c, typchk_exp e2 c, typchk_exp e3 c with
      | Some (NumT w), Some t1, Some t2 => if t1 == t2 then Some t1 else None
      | _, _, _ => None
      end
  | Extract n1 n2 e1 =>
      match typchk_exp e1 c with
      | Some (NumT w) => if andb (n2 <=? n1) (n1 <? w) then Some (NumT (N.succ (n1-n2))) else None
      | _ => None
      end
  | Concat e1 e2 =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some (NumT w1), Some (NumT w2) => Some (NumT (w1+w2))
      | _, _ => None
      end
  end.

(* Compute the meet of two input contexts. *)
Definition typctx_meet (c1 c2:typctx) v :=
  match c1 v, c2 v with
  | Some t1, Some t2 => if t1 == t2 then Some t1 else None
  | _, _ => None
  end.

(* Type-check a statement given a frame-context and initial context. *)
Fixpoint typchk_stmt (q:stmt) (c0 c:typctx): option typctx :=
  match q with
  | Nop => Some c
  | Move v e =>
      match typchk_exp e c with
      | Some t => match c0 v with
                  | None => Some (c[v:=Some t])
                  | Some t' => if t == t' then Some (c[v:=Some t]) else None
                  end
      | None => None
      end
  | Jmp e => match typchk_exp e c with Some (NumT _) => Some c | _ => None end
  | Exn _ => Some c
  | Seq q1 q2 => match typchk_stmt q1 c0 c with
                 | None => None
                 | Some c2 => typchk_stmt q2 c0 c2
                 end
  | If e q1 q2 =>
      match typchk_exp e c, typchk_stmt q1 c0 c, typchk_stmt q2 c0 c with
      | Some (NumT 1), Some c1, Some c2 => Some (typctx_meet c1 c2)
      | _, _, _ => None
      end
  | Rep e q1 =>
      match typchk_exp e c, typchk_stmt q1 c c with
      | Some (NumT _), Some _ => Some c
      | _, _ => None
      end
  end.


(* The expression type-checker is sound. *)
Theorem typchk_exp_sound:
  forall e c t, typchk_exp e c = Some t -> hastyp_exp c e t.
Proof.
  induction e; simpl; intros.

  (* Var *)
  apply TVar. assumption.

  (* Word *)
  destruct (n <? 2^w) eqn:LT.
    injection H; intro; subst. apply TWord, N.ltb_lt, LT.
    discriminate.

  (* Load *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (typchk_exp e2 c) as [t2|]; [destruct t2|]; try discriminate.
  destruct (w0 =? w1) eqn:EQ; [|discriminate].
  apply Neqb_ok in EQ. injection H; intro; subst.
  eapply TLoad.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* Store *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (typchk_exp e1 c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (typchk_exp e2 c) as [t2|]; [destruct t2|]; try discriminate.
  destruct (typchk_exp e3 c) as [t3|]; [destruct t3|]; try discriminate.
  destruct (w0 =? w1) eqn:EQ1; [|discriminate].
  destruct (w2 =? _) eqn:EQ2; [|discriminate].
  apply Neqb_ok in EQ1. apply Neqb_ok in EQ2. injection H; intro; subst.
  apply TStore.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.

  (* BinOp *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (typchk_exp e2 c) as [t2|]; [destruct t2|]; try discriminate.
  destruct (w =? w0) eqn:EQ; [|discriminate].
  apply Neqb_ok in EQ. injection H; intro; subst.
  apply TBinOp.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* UnOp *)
  specialize (IHe c).
  destruct (typchk_exp e c) as [t1|]; [destruct t1|]; try discriminate.
  injection H; intro; subst.
  apply TUnOp. apply IHe. reflexivity.

  (* Cast *)
  specialize (IHe c0).
  destruct (typchk_exp e c0) as [t1|]; [destruct t1|]; try discriminate.
  destruct c; destruct (_ <=? _) eqn:LE; try discriminate;
  apply N.leb_le in LE; injection H; intro; subst;
  (eapply TCast; [ apply IHe; reflexivity | exact LE ]).

  (* Let *)
  specialize (IHe1 c). destruct (typchk_exp e1 c); [|discriminate].
  eapply TLet.
    apply IHe1. reflexivity.
    apply IHe2. assumption.

  (* Unknown *)
  injection H; intro; subst. apply TUnknown.

  (* Ite *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (typchk_exp e1 c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (typchk_exp e2 c) as [t2|]; [|discriminate].
  destruct (typchk_exp e3 c) as [t3|]; [|discriminate].
  destruct (typ_eqdec t2 t3); [|discriminate].
  injection H; intro; subst.
  eapply TIte.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.

  (* Extract *)
  specialize (IHe c).
  destruct (typchk_exp e c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (n2 <=? n1) eqn:LE; [|discriminate]. apply N.leb_le in LE.
  destruct (n1 <? w) eqn:LT; [|discriminate]. apply N.ltb_lt in LT.
  injection H; intro; subst.
  eapply TExtract.
    apply IHe. reflexivity.
    exact LE.
    exact LT.

  (* Concat *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [t1|]; [destruct t1|]; try discriminate.
  destruct (typchk_exp e2 c) as [t2|]; [destruct t2|]; try discriminate.
  injection H; intro; subst.
  apply TConcat.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.

(* The meet of two contexts is bounded above by the contexts. *)
Lemma typctx_meet_subset:
  forall c1 c2, typctx_meet c1 c2 ⊆ c1.
Proof.
  intros c1 c2 v t H. unfold typctx_meet in H.
  destruct (c1 v) as [t1|]; [|discriminate].
  destruct (c2 v) as [t2|]; [|discriminate].
  destruct (t1 == t2). exact H. discriminate.
Qed.

(* Context-meet is commutative. *)
Lemma typctx_meet_comm:
  forall c1 c2, typctx_meet c1 c2 = typctx_meet c2 c1.
Proof.
  intros. extensionality v. unfold typctx_meet.
  destruct (c1 v), (c2 v); try reflexivity.
  destruct (t == t0).
    subst. destruct (t0 == t0). reflexivity. contradict n. reflexivity.
    destruct (t0 == t). contradict n. symmetry. assumption. reflexivity.
Qed.

(* Context-meet computes the greatest of the lower bounds of the inputs. *)
Lemma typctx_meet_lowbound:
  forall c0 c1 c2 (SS1: c0 ⊆ c1) (SS2: c0 ⊆ c2), c0 ⊆ typctx_meet c1 c2.
Proof.
  unfold "⊆", typctx_meet. intros.
  rewrite (SS1 _ _ H). rewrite (SS2 _ _ H).
  destruct (y == y); [|contradict n]; reflexivity.
Qed.

(* The type-checker preserves the frame context. *)
Lemma typchk_stmt_mono:
  forall c0 q c c' (TS: typchk_stmt q c0 c = Some c') (SS: c0 ⊆ c), c0 ⊆ c'.
Proof.
  induction q; simpl; intros.

  (* Nop *)
  injection TS; intro; subst. exact SS.

  (* Move *)
  destruct (typchk_exp e c) as [t|]; [|discriminate].
  destruct (c0 v) as [t'|] eqn:C0V.
    destruct (typ_eqdec t t').
      injection TS; intro; subst. intros v0 t0 H. destruct (v0 == v).
        subst v0. rewrite update_updated, <- C0V, <- H. reflexivity.
        rewrite update_frame by assumption. apply SS, H.
      discriminate.
    injection TS; intro; subst. intros v0 t0 H. destruct (v0 == v).
      subst v0. rewrite C0V in H. discriminate.
      rewrite update_frame by assumption. apply SS, H.

  (* Jmp *)
  destruct (typchk_exp e c) as [[t|]|]; try discriminate.
  injection TS; intro; subst. exact SS.

  (* Exn *)
  injection TS; intro; subst. exact SS.

  (* Seq *)
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  eapply IHq2. exact TS.
  eapply IHq1. exact TS1. exact SS.

  (* If *)
  destruct (typchk_exp e c) as [[[|[| |]]|]|]; try discriminate.
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (typchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; intro; subst.
  apply typctx_meet_lowbound.
    eapply IHq1. exact TS1. exact SS.
    eapply IHq2. exact TS2. exact SS.

  (* Rep *)
  destruct (typchk_exp e c) as [[|]|]; try discriminate.
  destruct (typchk_stmt q c c) eqn:TS1; [|discriminate].
  injection TS; intro; subst.
  exact SS.
Qed.

(* The statement type-checker is sound. *)
Theorem typchk_stmt_sound:
  forall q c0 c c' (SS: c0 ⊆ c) (TS: typchk_stmt q c0 c = Some c'),
  hastyp_stmt c0 c q c'.
Proof.
  induction q; intros; simpl in TS.

  (* Nop *)
  injection TS; intro; subst. apply TNop.

  (* Move *)
  destruct (typchk_exp e c) eqn:TE; [|discriminate].
  destruct (c0 v) eqn:C0V; [destruct (typ_eqdec t _)|];
  try (injection TS; intro); subst;
  first [ discriminate | apply TMove ].
    right. exact C0V. apply typchk_exp_sound. exact TE.
    left. exact C0V. apply typchk_exp_sound. exact TE.

  (* Jmp *)
  destruct (typchk_exp e c) as [t|] eqn:TE; [destruct t|]; try discriminate.
  injection TS; intro; subst.
  eapply TJmp. apply typchk_exp_sound. exact TE.

  (* Exn *)
  injection TS; intro; subst. apply TExn.

  (* Seq *)
  specialize (IHq1 c0 c). destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  specialize (IHq2 c0 c1). destruct (typchk_stmt q2 c0 c1); [|discriminate].
  injection TS; intro; subst.
  eapply TSeq.
    reflexivity.
    apply IHq1. exact SS. reflexivity.
    apply IHq2. eapply typchk_stmt_mono; eassumption. reflexivity.

  (* If *)
  destruct (typchk_exp e c) as [[[|[|p|]]|]|] eqn:TE; try discriminate.
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (typchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; intro; subst.
  eapply TIf.
    apply typctx_meet_subset.
    rewrite typctx_meet_comm. apply typctx_meet_subset.
    apply typchk_exp_sound. exact TE.
    apply IHq1. exact SS. exact TS1.
    apply IHq2. exact SS. exact TS2.

  (* Rep *)
  destruct (typchk_exp e c) as [[|]|] eqn:TE; try discriminate.
  specialize (IHq c c). destruct (typchk_stmt q c c) as [c1|] eqn:TS1; [|discriminate].
  injection TS; intro; subst.
  eapply TRep. all:cycle 1.
    apply typchk_exp_sound. exact TE.
    eapply hastyp_stmt_weaken. apply IHq. reflexivity. reflexivity. exact SS.
    eapply typchk_stmt_mono. exact TS1. reflexivity.
Qed.

(* Create a theorem that transforms a type-safety goal into an application of
   the type-checker.  This allows type-safety goals to be solved by any of
   Coq's fast reduction tactics, such as vm_compute or native_compute. *)
Corollary typchk_stmt_compute:
  forall q c (TS: if typchk_stmt q c c then True else False),
  exists c', hastyp_stmt c c q c'.
Proof.
  intros. destruct (typchk_stmt q c c) as [c'|] eqn:TS1.
    exists c'. apply typchk_stmt_sound. reflexivity. exact TS1.
    contradict TS.
Qed.

(* Attempt to automatically solve a goal of the form (welltyped_prog c p).
   Statements in p that cannot be type-checked automatically (using context-
   meets at conditionals and the incoming context as the fixpoint of loops)
   are left as subgoals for the user to solve.  For most ISAs, this should
   not happen; the algorithm should fully solve all the goals. *)
Ltac Picinae_typecheck :=
  lazymatch goal with [ |- welltyped_prog _ _ ] =>
    let s := fresh "s" in let a := fresh "a" in
    intros s a;
    destruct a as [|a]; repeat first [ exact I | destruct a as [a|a|] ];
    try (apply typchk_stmt_compute; vm_compute; exact I)
  | _ => fail "goal is not of the form (welltyped_prog c p)"
  end.

End PICINAE_STATICS.


Module PicinaeStatics (IL: PICINAE_IL) <: PICINAE_STATICS IL.
  Include PICINAE_STATICS IL.
End PicinaeStatics.
