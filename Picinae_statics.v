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

Module PicinaeStatics (Arch: Architecture).

(* This module proves that the semantics of the IL are type-safe in the sense that
   programs whose constants have proper bitwidths never produce variable values or
   expressions that exceed their declared bitwidths as they execute.  This is
   important for (1) providing assurance that the semantics are correctly defined,
   and (2) proving practical results that rely upon the assumption that machine
   registers and memory contents always have values of appropriate bitwidths. *)

Module PTheory := PicinaeTheory Arch.
Export PTheory.
Open Scope N.

(* A typing context is a partial map from variables to types. *)
Definition typctx := var -> option typ.

(* The bitwidth of the result of a binary operation *)
Definition widthof_binop (bop:binop_typ) (w:bitwidth) : bitwidth :=
  match bop with
  | OP_PLUS | OP_MINUS | OP_TIMES | OP_DIVIDE | OP_SDIVIDE | OP_MOD | OP_SMOD
  | OP_LSHIFT | OP_RSHIFT | OP_ARSHIFT | OP_AND | OP_OR | OP_XOR => w
  | OP_EQ | OP_NEQ | OP_LT | OP_LE | OP_SLT | OP_SLE => 1
  end.

(* Type-check an expression in a typing context, returning its type. *)
Inductive typof_exp (c:typctx): exp -> typ -> Prop :=
| TVar (v:var) (t:typ)
       (CV: c v = Some t):
       typof_exp c (Var v) t
| TWord (n:N) (w:bitwidth)
        (LT: n < 2^w):
        typof_exp c (Word n w) (NumT w)
| TLoad (e1 e2:exp) (en:endianness) (len mw:bitwidth)
        (T1: typof_exp c e1 (MemT mw)) (T2: typof_exp c e2 (NumT mw)):
        typof_exp c (Load e1 e2 en len) (NumT (Mb*len))
| TStore (e1 e2 e3:exp) (en:endianness) (len mw:bitwidth)
         (T1: typof_exp c e1 (MemT mw)) (T2: typof_exp c e2 (NumT mw))
         (T3: typof_exp c e3 (NumT (Mb*len))):
         typof_exp c (Store e1 e2 e3 en len) (MemT mw)
| TBinOp (bop:binop_typ) (e1 e2:exp) (w:bitwidth)
         (T1: typof_exp c e1 (NumT w)) (T2: typof_exp c e2 (NumT w)):
         typof_exp c (BinOp bop e1 e2) (NumT (widthof_binop bop w))
| TUnOp (uop:unop_typ) (e:exp) (w:bitwidth)
        (T1: typof_exp c e (NumT w)):
        typof_exp c (UnOp uop e) (NumT w)
| TCast (ct:cast_typ) (w w':bitwidth) (e:exp)
        (T1: typof_exp c e (NumT w))
        (LE: match ct with CAST_UNSIGNED | CAST_SIGNED => w <= w'
                         | CAST_HIGH | CAST_LOW => w' <= w end):
        typof_exp c (Cast ct w' e) (NumT w')
| TLet (v:var) (e1 e2:exp) (t1 t2:typ)
       (T1: typof_exp c e1 t1) (T2: typof_exp (c[v:=Some t1]) e2 t2):
       typof_exp c (Let v e1 e2) t2
| TUnknown (t:typ):
           typof_exp c (Unknown t) t
| TIte (e1 e2 e3:exp) (w:bitwidth) (t:typ)
       (T1: typof_exp c e1 (NumT w)) (T2: typof_exp c e2 t) (T3: typof_exp c e3 t):
       typof_exp c (Ite e1 e2 e3) t
| TExtract (w n1 n2:bitwidth) (e1:exp)
           (T1: typof_exp c e1 (NumT w)) (LO: n2 <= n1) (HI: n1 < w):
           typof_exp c (Extract n1 n2 e1) (NumT (N.succ (n1-n2)))
| TConcat (e1 e2:exp) (w1 w2:N)
          (T1: typof_exp c e1 (NumT w1)) (T2: typof_exp c e2 (NumT w2)):
          typof_exp c (Concat e1 e2) (NumT (w1+w2)).

(* Static semantics for statements:
   Defining a sound statement typing semantics is tricky for two reasons:

   (1) There are really two kinds of IL variables: (a) those that encode cpu state
   (which are always initialized, and whose types are fixed), and (b) temporary
   variables introduced during lifting to IL (which are not guaranteed to be
   initialized, and whose types may vary across different instruction encodings.

   We therefore use separate contexts c0 and c to model the two kinds.  Context
   c0 models the cpu state variables, while c models all variables.  Context c
   therefore usually subsumes c0, and is always consistent with c0 (i.e., the
   join of c and c0 is always a valid context).  This consistency is enforced
   by checking assigned value types against c0 at every Move, irrespective of c.

   (2) Since variable initialization states are mutable, we need static rules
   that support meets and joins of contexts.  But a general weakening rule is
   inconveniently broad; it hampers syntax-directed inductive proofs, since it
   is potentially applicable to all statement forms during inversions.

   To avoid this, we instead define a strategically chosen weakening clause
   within the sequence typing rule (TSeq), along with a fixed point requirement
   for loops (TWhile).  An IL program that only assigns values of one type to
   each variable per instruction encoding can be safely type-checked by ignoring
   both clauses; the fixed point condition is automatically satisfied if the
   weakening clause is never utilized.  But including these two clauses yields
   a provably type-safe semantics because the weakening clause adds just enough
   flexibility to prove satisfaction of the fixed point requirement without
   having to cope with a fully generalized weakening rule. *)

Inductive typof_stmt (c0 c:typctx): stmt -> typctx -> Prop :=
| TNop: typof_stmt c0 c Nop c
| TMove v t e (CV: c0 v = None \/ c0 v = Some t) (TE: typof_exp c e t):
    typof_stmt c0 c (Move v e) (c[v:=Some t])
| TJmp e w (TE: typof_exp c e (NumT w)): typof_stmt c0 c (Jmp e) c
| TCpuExn ex: typof_stmt c0 c (CpuExn ex) c
| TSeq q1 q2 c1 c2 c' (SS: c2 ⊆ c1)
       (TS1: typof_stmt c0 c q1 c1) (TS2: typof_stmt c0 c2 q2 c'):
    typof_stmt c0 c (Seq q1 q2) c'
| TWhile e q c' (SS: c ⊆ c')
    (TE: typof_exp c e (NumT 1)) (TS: typof_stmt c0 c q c'):
    typof_stmt c0 c (While e q) c
| TIf e q1 q2 c1 c2 c' (SS1: c' ⊆ c1) (SS2: c' ⊆ c2)
      (TE: typof_exp c e (NumT 1))
      (TS1: typof_stmt c0 c q1 c1) (TS2: typof_stmt c0 c q2 c2):
    typof_stmt c0 c (If e q1 q2) c'.

(* A program is well-typed if all its statements are well-typed. *)
Definition welltyped_prog (c0:typctx) (p:program) : Prop :=
  forall a, match p a with None => True | Some (_,q) =>
              exists c', typof_stmt c0 c0 q c' end.


(* These short lemmas are helpful when automating type-checking in tactics. *)
Lemma typchk_binop:
  forall bop c e1 e2 w w' (W: widthof_binop bop w = w')
         (T1: typof_exp c e1 (NumT w)) (T2: typof_exp c e2 (NumT w)),
  typof_exp c (BinOp bop e1 e2) (NumT w').
Proof.
  intros. rewrite <- W. apply TBinOp; assumption.
Qed.

Lemma typchk_extract:
  forall w c n1 n2 e1 w' (W: N.succ (n1-n2) = w')
         (T1: typof_exp c e1 (NumT w)) (LO: n2 <= n1) (HI: n1 < w),
  typof_exp c (Extract n1 n2 e1) (NumT w').
Proof.
  intros. rewrite <- W. apply TExtract with (w:=w); assumption.
Qed.

Lemma typchk_concat:
  forall c e1 e2 w1 w2 w' (W: w1+w2 = w')
         (T1: typof_exp c e1 (NumT w1)) (T2: typof_exp c e2 (NumT w2)),
  typof_exp c (Concat e1 e2) (NumT w').
Proof.
  intros. rewrite <- W. apply TConcat; assumption.
Qed.


(* Type-checking of expressions and statements is deterministic. *)

Theorem typof_exp_deterministic:
  forall e c t1 t2 (TE1: typof_exp c e t1) (TE2: typof_exp c e t2),
  t1 = t2.
Proof.
  intros. revert t2 TE2. dependent induction TE1; intros; inversion TE2; subst;
  try reflexivity.

  rewrite CV in CV0. injection CV0. trivial.

  apply IHTE1_1. assumption.

  apply IHTE1_1 in T1. injection T1. intro. subst. reflexivity.

  apply IHTE1. assumption.

  apply IHTE1_2. apply IHTE1_1 in T1. subst. assumption.

  apply IHTE1_2. assumption.

  apply IHTE1_1 in T1. apply IHTE1_2 in T2.
  injection T1. injection T2. intros. subst. reflexivity.
Qed.

(* Expression typing contexts can be safely weakened. *)
Theorem typof_exp_weaken:
  forall c1 c2 e t (TE: typof_exp c1 e t) (SS: c1 ⊆ c2),
  typof_exp c2 e t.
Proof.
  intros. revert c2 SS. dependent induction TE; intros; econstructor;
  try (try first [ apply IHTE | apply IHTE1 | apply IHTE2 | apply IHTE3 | apply SS ]; assumption).

  apply IHTE2. unfold update. intros v0 t CV. destruct (vareq v0 v).
    assumption.
    apply SS. assumption.
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
   code programs because typically we want to prove that no stuck states are
   reachable, and conclude from this that there are no access violations and
   that the assumptions imply the assertions.  This is only possible if we can
   rule out stuck states introduced by a failure of BAP to lift the native
   code to valid IL code.  By type-checking the IL code prior to subsequent
   analysis, we provably preclude all but the stuck states of interest. *)


(* Helper lemmas for proving upper bounds on various operations *)

Lemma typof_towidth:
  forall w n, typof_val (towidth w n) (NumT w).
Proof.
  intros. apply TVN.
  apply N.mod_upper_bound.
  apply N.pow_nonzero.
  intro. discriminate.
Qed.

Lemma div_bound: forall n1 n2, N.div n1 n2 <= n1.
Proof.
  intros.
  destruct n2. destruct n1. reflexivity. apply N.le_0_l.
  apply N.div_le_upper_bound. discriminate 1.
  destruct n1. reflexivity.
  unfold N.le. simpl. change p0 with (1*p0)%positive at 1. rewrite Pos.mul_compare_mono_r.
  destruct p; discriminate 1.
Qed.

Remark Nlt_0_pow2: forall p, 0 < 2^p.
Proof. intros. apply N.neq_0_lt_0, N.pow_nonzero. discriminate 1. Qed.

Remark Zlt_0_pow2: forall p, (0 < Z.of_N (2^p))%Z.
Proof. intro. rewrite <- N2Z.inj_0. apply N2Z.inj_lt. apply Nlt_0_pow2. Qed.

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


(* Binary operations on well-typed values yield well-typed values. *)
Theorem typesafe_binop:
  forall bop n1 n2 w
         (TV1: typof_val (VaN n1 w) (NumT w)) (TV2: typof_val (VaN n2 w) (NumT w)),
  typof_val (eval_binop bop w n1 n2) (NumT (widthof_binop bop w)).
Proof.
  intros. destruct bop; try first [ apply typof_towidth | apply TVN, bit_bound ];
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
         (TV: typof_val (VaN n w) (NumT w)),
  typof_val (eval_unop uop n w) (NumT w).
Proof.
  intros. destruct uop; apply TVN.

  (* NEG *)
  apply N.mod_upper_bound, N.pow_nonzero. discriminate 1.

  (* NOT *)
  apply lnot_bound, value_bound. assumption.
Qed.

(* Casts of well-typed values yield well-typed values. *)
Theorem typesafe_cast:
  forall c n w w' (TV: typof_val (VaN n w) (NumT w))
    (T: match c with CAST_UNSIGNED | CAST_SIGNED => w<=w'
                   | CAST_HIGH | CAST_LOW => w'<=w end),
  typof_val (VaN (cast c w w' n) w') (NumT w').
Proof.
  intros. inversion TV. subst. destruct c; simpl.

  (* LOW *)
  apply typof_towidth.

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
  forall mw len m a e (TV: typof_val (VaM m mw) (MemT mw)),
  typof_val (VaN (getmem e len m a) (Mb*len)) (NumT (Mb*len)).
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
         (TV1: typof_val (VaM m mw) (MemT mw))
         (TV3: typof_val (VaN v (Mb*len)) (NumT (Mb*len))),
  typof_val (VaM (setmem e len m a v) mw) (MemT mw).
Proof.
  intros. apply TVM, setmem_welltyped.
    eapply mem_welltyped. eassumption.
    apply value_bound. assumption.
Qed.


(* Context c "models" a store s if all variables in c have values in s
   that are well-typed with respect to c. *)
Definition models (c:typctx) (s:store) : Prop :=
  forall v t (CV: c v = Some t),
  exists u, s v = Some u /\ typof_val u t.

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

(* Well-typedness of while-loop is preserved by unrolling. *)
Remark welltyped_while:
  forall e q c0 c,
  typof_stmt c0 c (While e q) c ->
  typof_stmt c0 c (If e (Seq q (While e q)) Nop) c.
Proof.
  intros. inversion H; subst.
  apply TIf with (c1:=c) (c2:=c); try reflexivity; try assumption.
    apply TSeq with (c1:=c') (c2:=c); assumption.
    apply TNop.
Qed.

(* Every result of evaluating a well-typed expression is a well-typed value. *)
Lemma preservation_eval_exp:
  forall {s e c t u}
         (MCS: models c s) (TE: typof_exp c e t) (E: eval_exp s e u),
  typof_val u t.
Proof.
  intros. revert s u MCS E. dependent induction TE; intros;
  inversion E; subst;
  repeat (match goal with [ IH: forall _ _, models _ _ -> eval_exp _ ?E _ -> typof_val _ _,
                            M: models _ ?S,
                            EE: eval_exp ?S ?E _ |- _ ] =>
            specialize (IH S _ MCS EE); try (inversion IH; [idtac]; subst) end).

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
    unfold update. intros v0 t0 VEQT. destruct (vareq v0 v).
      exists u1. split. reflexivity. injection VEQT. intro. subst t0. assumption.
      apply MCS in VEQT. assumption.
  revert CS' E2. apply IHTE2.

  (* Unknown *)
  assumption.

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
         (MCS: models c s) (T: typof_exp c e t),
  exists u, eval_exp s e u.
Proof.
  intros. revert s MCS. dependent induction T; intros;
  repeat match reverse goal with [ IH: forall _, models ?C _ -> exists _, eval_exp _ ?E _,
                                    M: models ?C ?S,
                                    T: typof_exp ?C ?E _ |- _ ] =>
    specialize (IH S M);
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
  eexists. eapply ELoad; try eassumption. intros. apply RW.

  (* Store *)
  eexists. eapply EStore; try eassumption. intros. apply RW.

  (* BinOp *)
  eexists. apply EBinOp; eassumption.

  (* UnOp *)
  eexists. apply EUnOp; eassumption.

  (* Cast *)
  eexists. apply ECast; eassumption.

  (* Let *)
  assert (CS': models (c[v:=Some t1]) (s[v:=Some u])).
    unfold update. intros v0 t0 VEQT. destruct (vareq v0 v).
      exists u. split. reflexivity. injection VEQT. intro. subst t0. assumption.
      apply MCS in VEQT. assumption.
  edestruct IHT2 as [u2 EE2].
    apply CS'.
    exists u2. eapply ELet; eassumption.

  (* Unknown *)
  destruct t.
    exists (VaN 0 w). apply EUnknown, TVN, Nlt_0_pow2.
    exists (VaM (fun _ => 0) w). apply EUnknown, TVM. intro. apply Nlt_0_pow2.

  (* Ite *)
  eexists (match n with N0 => u0 | _ => u end).
  apply EIte with (n1:=n) (w1:=w). assumption. destruct n; assumption.

  (* Extract *)
  eexists. apply EExtract; eassumption.

  (* Concat *)
  eexists. apply EConcat; eassumption.
Qed.

(* Statement execution preserves the modeling relation. *)
Lemma preservation_exec_stmt:
  forall {m s q c0 c c' s'}
         (MCS: models c s) (T: typof_stmt c0 c q c') (XS: exec_stmt s q m s' None),
  models c' s'.
Proof.
  intros. revert c c' MCS T. dependent induction XS; intros; inversion T; subst;
  try assumption.

  unfold update. intros v0 t0 T0. destruct (vareq v0 v).
    subst. injection T0; intro; subst. exists u. split. reflexivity. apply (preservation_eval_exp MCS TE E).
    apply MCS; assumption.

  apply IHXS2 with (c:=c2).
    reflexivity.
    apply models_subset with (c:=c1).
      apply IHXS1 with (c:=c). reflexivity. assumption. assumption.
      assumption.
    assumption.

  apply IHXS with (c:=c') (c':=c').
    reflexivity.
    assumption.
    apply welltyped_while. assumption.

  destruct c.
    apply models_subset with (c:=c3).
      apply IHXS with (c:=c1). reflexivity. assumption. assumption.
      assumption.
    apply models_subset with (c:=c2).
      apply IHXS with (c:=c1). reflexivity. assumption. assumption.
      assumption.
Qed.

(* Execution also preserves modeling the frame context c0. *)
Lemma pres_frame_exec_stmt:
  forall {m s q c0 c c' s' x} (MC0S: models c0 s) (MCS: models c s)
         (T: typof_stmt c0 c q c') (XS: exec_stmt s q m s' x),
  models c0 s'.
Proof.
  intros. revert c c' MCS T. dependent induction XS; intros;
  try assumption;
  inversion T; subst.

  intros v0 t0 CV0. unfold update. destruct (vareq v0 v).
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

  apply IHXS with (c:=c') (c':=c'); try assumption.
  apply welltyped_while. assumption.

  destruct c.
    apply IHXS with (c:=c1) (c':=c3); assumption.
    apply IHXS with (c:=c1) (c':=c2); assumption.
Qed.

(* Well-typed statements never get "stuck" except for memory access violations.
   They either hit the recursion limit, exit, or run to completion. *)
Lemma progress_exec_stmt:
  forall {s q c0 c c'} n
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: typof_stmt c0 c q c'),
  exists s' x, exec_stmt s q n s' x.
Proof.
  intros. revert s q c c' MCS T. induction n; intros.
    exists s,(Some Unfinished). apply XZero.

    destruct q; try (inversion T; subst).

      (* Nop *)
      exists s,None. apply XNop.

      (* Move *)
      assert (E:=progress_eval_exp RW MCS TE). destruct E as [u E].
      exists (s[v:=Some u]),None. apply XMove. assumption.

      (* Jmp *)
      assert (E:=progress_eval_exp RW MCS TE). destruct E as [u E].
      assert (TV:=preservation_eval_exp MCS TE E). inversion TV as [a' w'|]; subst.
      exists s,(Some (Exit a')). apply XJmp with (w:=w). assumption.

      (* CpuExn *)
      exists s,(Some (Exn i)). apply XExn.

      (* Seq *)
      assert (XS1:=IHn s q1 c c1 MCS TS1). destruct XS1 as [s2 [x1 XS1]].
      destruct x1 as [x1|].

        destruct x1.
          exists s2,(Some Unfinished). apply XSeq1. assumption.
          exists s2,(Some (Exit a)). apply XSeq1. assumption.
          exists s2,(Some (Exn i)). apply XSeq1. assumption.

        assert (MCS2:=preservation_exec_stmt MCS TS1 XS1).
        apply models_subset with (c':=c2) in MCS2; try assumption.
        assert (XS2:=IHn s2 q2 c2 c' MCS2 TS2). destruct XS2 as [s' [x XS2]]. 
        exists s',x. apply XSeq2 with (s2:=s2); assumption.

      (* While *)
      specialize IHn with (s:=s) (q:=If e (Seq q (While e q)) Nop) (c:=c') (c':=c').
      apply welltyped_while in T.
      destruct (IHn MCS T) as [s' [x XS]].
      exists s',x. apply XWhile. assumption.

      (* If *)
      assert (E:=progress_eval_exp RW MCS TE). destruct E as [u E].
      assert (TV:=preservation_eval_exp MCS TE E). inversion TV as [cnd w|]; subst.
      destruct cnd.
        destruct (IHn s q2 c c2 MCS TS2) as [s'2 [x2 XS2]]. exists s'2,x2. apply XIf with (c:=0); assumption.
        destruct (IHn s q1 c c1 MCS TS1) as [s'1 [x1 XS1]]. exists s'1,x1. apply XIf with (c:=N.pos p); assumption.
Qed.

(* Well-typed programs preserve the modeling relation at every execution step. *)
Theorem preservation_exec_prog:
  forall p c s m n a s' x (MCS: models c s)
         (WP: welltyped_prog c p) (XS: exec_prog p a s m n s' x),
  models c s'.
Proof.
  intros. revert a s x MCS XS. induction n; intros; inversion XS; clear XS; subst.
    assumption.
    eapply IHn.
      specialize (WP a). rewrite LU in WP. destruct WP as [c' TS]. eapply pres_frame_exec_stmt.
        exact MCS. exact MCS. exact TS. exact XS0.
      exact XP.
    specialize (WP a). rewrite LU in WP. destruct WP as [c' TS]. eapply pres_frame_exec_stmt.
      exact MCS. exact MCS. exact TS. exact XS0.
Qed.

(* Well-typed programs never get "stuck" except for memory access violations.
   They hit the recursion limit, exit, or run to completion.  They never get
   "stuck" due to a runtime type-mismatch. *)
Theorem progress_exec_prog:
  forall p c0 s0 m n a s1 a'
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c0 s0) (WP: welltyped_prog c0 p)
         (XP: exec_prog p a s0 m n s1 (Exit a')) (IL: p a' <> None),
  exists s' x, exec_prog p a s0 m (S n) s' x.
Proof.
  intros.
  assert (WPA':=WP a'). destruct (p a') as [(sz,q)|] eqn:IL'; [|contradict IL; reflexivity]. clear IL.
  destruct WPA' as [c' T]. eapply progress_exec_stmt in T.
    destruct T as [s' [x XS]]. exists s'. eapply exec_prog_append in XS; [|exact XP | exact IL'].
      destruct x as [e|]; [destruct e|]; eexists; exact XS.
    exact RW.
    eapply preservation_exec_prog. exact MCS. exact WP. exact XP.
Qed.

(* Attempt to automatically solve a goal of one of the following forms:
   (1) welltyped_prog c p
   (2) typof_stmt c0 c q ?c'
   (3) typof_exp c e ?t
   This tactic only succeeds on common-case programs, statements, and expressions.
   More exotic goals will need manual proof effort. *)
Ltac Picinae_typecheck :=
  repeat lazymatch goal with
  | [ |- welltyped_prog _ _ ] => let a := fresh "a" in
      intro a;
      destruct a as [|a]; repeat first [ exact I | destruct a as [a|a|] ];
      eexists
  | [ |- typof_exp _ (BinOp _ _ _) _ ] => eapply typchk_binop
  | [ |- typof_exp _ (Extract _ _ _) _ ] => eapply typchk_extract
  | [ |- typof_exp _ (Concat _ _) _ ] => eapply typchk_concat
  | [ |- typof_stmt _ _ _ _ ] => econstructor
  | [ |- typof_exp _ _ _ ] => econstructor
  | [ |- update _ _ _ _ _ = _ ] => repeat (rewrite update_frame; [|discriminate 1]);
                                   solve [ apply update_updated | reflexivity ]
  | [ |- _ = _ \/ _ = _ ] => solve [ left;reflexivity | right;reflexivity ]
  | [ |- _ ⊆ _ ] => reflexivity
  | [ |- _ = _ ] => reflexivity
  | [ |- _ < _ ] => reflexivity
  | [ |- _ <= _ ] => discriminate 1
  end.

End PicinaeStatics.
