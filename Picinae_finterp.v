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
   Functional interpretation of IL programs.           MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   Then compile this module with menu option                MMMMMMMMMMM7..ZNOOMZ
   Compile->Compile_buffer.                                  MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
                                                               $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Import Picinae_theory.
Require Import NArith.
Require Import ZArith.

(* Functional Interpretation of Programs:
   This module defines an IL interpreter that is purely functional instead of inductive.  Since programs
   can be non-deterministic (if there are Unknown expressions), this interpreter only computes one possible
   value of each variable.  We then prove that this result is correct according to the operational semantics.
   When there are no unknowns, determinism of the semantics (proved above) proves that the result is precise.
   This facilitates a series of tactics that can interpret common-case expressions and statements in proofs
   to automatically infer the resulting store after execution of each assembly language instruction.

   In order to help Coq expression simplification to infer a value for each symbolic expression, we define
   our interpreter in terms of "untyped values" (uvalues), which always contain both a memory value and a
   numeric value.  This allows the interpreter to progress even when Coq can't automatically infer an
   expression's type. *)

Inductive uvalue := VaU (z:bool) (m:addr->N) (n:N) (w:N).

Definition zstore (_:addr) := 0.

Definition uvalue_of (v:value) :=
  match v with
  | VaN n w => VaU true zstore n w
  | VaM m w => VaU false m 0 w
  end.

Definition of_uvalue (v:uvalue) :=
  match v with VaU z m n w => if z then VaN n w else VaM m w end.

Definition utowidth (w n:N) : uvalue :=
  VaU true zstore (N.modulo n (2^w)) w.

Definition utobit (b:bool) : uvalue :=
  VaU true zstore (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth w (n1+n2)
  | OP_MINUS => utowidth w (2^w + n1 - n2)
  | OP_TIMES => utowidth w (n1*n2)
  | OP_DIVIDE => VaU true zstore (n1/n2) w
  | OP_SDIVIDE => VaU true zstore (sbop Z.quot w n1 n2) w
  | OP_MOD => VaU true zstore (N.modulo n1 n2) w
  | OP_SMOD => VaU true zstore (sbop Z.rem w n1 n2) w
  | OP_LSHIFT => utowidth w (N.shiftl n1 n2)
  | OP_RSHIFT => VaU true zstore (N.shiftr n1 n2) w
  | OP_ARSHIFT => VaU true zstore (ashiftr w n1 n2) w
  | OP_AND => VaU true zstore (N.land n1 n2) w
  | OP_OR => VaU true zstore (N.lor n1 n2) w
  | OP_XOR => VaU true zstore (N.lxor n1 n2) w
  | OP_EQ => utobit (n1 =? n2)
  | OP_NEQ => utobit (negb (n1 =? n2))
  | OP_LT => utobit (n1 <? n2)
  | OP_LE => utobit (n1 <=? n2)
  | OP_SLT => utobit (slt w n1 n2)
  | OP_SLE => utobit (sle w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => utowidth w ((2^w) - n)
  | OP_NOT => VaU true zstore (N.lnot n w) w
  end.

Definition uget (v:option value) : uvalue :=
  match v with None => VaU true zstore 0 0
             | Some u => uvalue_of u
  end.

Lemma fold_uget:
  forall v, match v with None => VaU true zstore 0 0
                       | Some u => uvalue_of u
            end = uget v.
Proof. intros. reflexivity. Qed.

Lemma uvalue_inv: forall u, of_uvalue (uvalue_of u) = u.
Proof.
  intros. destruct u; reflexivity.
Qed.

Definition canonical_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then m = zstore else n = 0 end.

Lemma can_uvalue_inv: forall u (C: canonical_uvalue u), uvalue_of (of_uvalue u) = u.
Proof.
  intros. destruct u. destruct z; simpl in C; subst; reflexivity.
Qed.

Lemma canonical_conv:
  forall v, canonical_uvalue (uvalue_of v).
Proof.
  intro. destruct v; reflexivity.
Qed.

Lemma canonical_uget:
  forall v, canonical_uvalue (uget v).
Proof.
  intros. destruct v.
    apply canonical_conv.
    reflexivity.
Qed.


Module Type PICINAE_FINTERP (IL: PICINAE_IL).

Import IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.

Definition bits_of_mem len := N.mul Mb len.

Fixpoint feval_exp (e:exp) (s:store) : uvalue :=
  match e with
  | Var v => uget (s v)
  | Word n w => VaU true zstore n w
  | Load e1 e2 en len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ _, VaU _ _ n _ => VaU true zstore (getmem en len m n) (bits_of_mem len)
      end
  | Store e1 e2 e3 en len =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ m _ mw, VaU _ _ a _, VaU _ _ v _ => VaU false (setmem en len m a v) 0 mw
      end
  | BinOp bop e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w, VaU _ _ n2 _ => feval_binop bop w n1 n2
      end
  | UnOp uop e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => feval_unop uop n w
      end
  | Cast c w' e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast c w w' n) w'
      end
  | Let v e1 e2 => feval_exp e2 (update s v (Some (of_uvalue (feval_exp e1 s))))
  | Unknown _ => VaU true zstore 0 0
  | Ite e1 e2 e3 =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ _ n1 _, VaU b2 m2 n2 w2, VaU b3 m3 n3 w3 =>
          VaU (if n1 then b3 else b2) (if n1 then m3 else m2) (if n1 then n3 else n2) (if n1 then w3 else w2)
      end
  | Extract n1 n2 e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                             (cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2))
      end
  | Concat e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w1, VaU _ _ n2 w2 => VaU true zstore (N.lor (N.shiftl n1 w2) n2) (w1+w2)
      end
  end.

Definition NoMemAcc := True.
Definition MemAcc (P: store -> addr -> Prop) h s a len :=
  forall n, n < len -> h (a+n) = Some tt /\ P s (a+n).

Fixpoint memacc_exp h e s : Prop :=
  match e with
  | Load e1 e2 _ len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc mem_readable h s a len
      end
  | Store e1 e2 _ _ len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc mem_writable h s a len
      end
  | Var _ | Word _ _ | Unknown _ => NoMemAcc
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => memacc_exp h e1 s
  | BinOp _ e1 e2 | Concat e1 e2 => memacc_exp h e1 s /\ memacc_exp h e2 s
  | Let v e1 e2 => memacc_exp h e1 s /\ memacc_exp h e2 (update s v (Some (of_uvalue (feval_exp e1 s))))
  | Ite e1 e2 e3 =>
      match feval_exp e1 s with
      | VaU _ _ n w => if n then memacc_exp h e3 s else memacc_exp h e2 s
      end
  end.

Fixpoint exp_known e :=
  match e with
  | Var _ | Word _ _ => true
  | Unknown _ => false
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => exp_known e1
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ => if exp_known e1 then exp_known e2 else false
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ => if exp_known e1 then (if exp_known e2 then exp_known e3 else false) else false
  end.


Lemma canonical_feval:
   forall e s, canonical_uvalue (feval_exp e s).
Proof.
  induction e; intros; simpl;
  repeat match goal with |- context [ feval_exp ?e ?s ] => destruct (feval_exp e s) eqn:? end;
  try reflexivity.
  apply canonical_uget.
  destruct b; reflexivity.
  destruct u; reflexivity.
  rewrite <- Hequ. apply IHe2.
  destruct n;
    match goal with [ H: _ = ?u |- _ ?u ] => rewrite <- H; generalize s; assumption end.
Qed.

Theorem reduce_binop:
  forall bop w n1 n2, eval_binop bop w n1 n2 = of_uvalue (feval_binop bop w n1 n2).
Proof.
  intros. destruct bop; reflexivity.
Qed.

Theorem reduce_unop:
  forall uop w n, eval_unop uop w n = of_uvalue (feval_unop uop w n).
Proof.
  intros. destruct uop; reflexivity.
Qed.

Theorem reduce_exp:
  forall h e s u (K: exp_known e = true) (E: eval_exp h s e u), u = of_uvalue (feval_exp e s).
Proof.
  induction e; intros; inversion E; clear E; subst; simpl;
  simpl in K; repeat (apply andb_prop in K; let K':=fresh "K" in destruct K as [K' K]);
  repeat match goal with [ IH: forall _ _, exp_known ?e = _ -> _, K: exp_known ?e = _, E: eval_exp _ _ ?e _ |- _ ] =>
    apply (IH _ _ K) in E;
    try (let b := fresh "b" in destruct (feval_exp e _) as [b ? ? ?]; destruct b; try discriminate E; injection E as)
  end; subst; try reflexivity.

    rewrite SV. symmetry. apply uvalue_inv.

    apply reduce_binop.

    apply reduce_unop.

    discriminate K.

    destruct n.
      apply (IHe3 _ _ K) in E'. destruct (feval_exp e2 s). destruct (feval_exp e3 _). subst u. reflexivity.
      apply (IHe2 _ _ K1) in E'. destruct (feval_exp e2 _). destruct (feval_exp e3 _). subst u. reflexivity.
Qed.

Theorem memacc_exp_true:
  forall h e s u (K: exp_known e = true) (E: eval_exp h s e u),
  memacc_exp h e s.
Proof.
  induction e; intros; try exact I;
    try (unfold exp_known in K; fold exp_known in K; apply andb_prop in K; destruct K as [K1 K2]);
    inversion E; subst;
    unfold memacc_exp; fold memacc_exp;
    try first [ eapply IHe; [ exact K | exact E1 ]
              | split; [ eapply IHe1; [ exact K1 | exact E1 ]
                       | eapply IHe2; [ exact K2 | exact E2 ] ] ].

  (* Load *)
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. rewrite <- E1, <- E2. exact R.

  (* Store *)
  apply andb_prop, proj1 in K2.
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. rewrite <- E1, <- E2. exact W.

  (* Let *)
  split.
    eapply IHe1. exact K1. exact E1.
    eapply IHe2. exact K2. apply reduce_exp in E1; [|exact K1]. rewrite <- E1. exact E2.

  (* Ite *)
  apply reduce_exp in E1; [|exact K1]. apply (f_equal uvalue_of) in E1. rewrite can_uvalue_inv in E1 by apply canonical_feval.
  rewrite <- E1. simpl. apply andb_prop in K2. destruct n1.
    eapply IHe3. exact (proj2 K2). exact E'.
    eapply IHe2. exact (proj1 K2). exact E'.
Qed.


(* With the above, we can now reduce common-case exec_stmt hypotheses into hypotheses of the
   form s' = ... /\ x' = ..., which allows us to infer the final store s' and exit state x'
   and substitute them away throughout the proof context. *)

Lemma reduce_seq_move:
  forall x1 h s1 v e q s1' (XS: exec_stmt h s1 (Seq (Move v e) q) s1' x1),
  if exp_known e then
    (let u := of_uvalue (feval_exp e s1) in exec_stmt h (s1[v:=Some u]) q s1' x1) /\
    memacc_exp h e s1
  else
    exists u, exec_stmt h (s1[v:=Some u]) q s1' x1.
Proof.
  intros. inversion XS; subst.
    inversion XS0; subst.

    inversion XS1; subst. destruct (exp_known e) eqn:K.
      split.
        eapply reduce_exp in E. subst u. exact XS0. exact K.
        eapply memacc_exp_true. exact K. exact E.
      eexists. exact XS0.
Qed.

Lemma reduce_nop:
  forall x1 h s1 s1' (XS: exec_stmt h s1 Nop s1' x1),
  s1' = s1 /\ x1 = None.
Proof.
  intros. inversion XS; subst. split; reflexivity.
Qed.

Lemma reduce_move:
  forall x1 h s1 v e s1' (XS: exec_stmt h s1 (Move v e) s1' x1),
  if exp_known e then
    ((let u := of_uvalue (feval_exp e s1) in s1' = s1[v:=Some u]) /\ x1 = None) /\
    memacc_exp h e s1
  else exists u, (s1' = s1[v:=Some u] /\ x1 = None).
Proof.
  intros. inversion XS; subst. destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E. rewrite E. split; reflexivity. exact K.
      eapply memacc_exp_true. exact K. exact E.
    exists u. split; reflexivity.
Qed.

Lemma reduce_jmp:
  forall x1 h s1 e s1' (XS: exec_stmt h s1 (Jmp e) s1' x1),
  if exp_known e then
    (s1' = s1 /\ x1 = Some (Exit (match feval_exp e s1 with VaU _ _ a _ => a end))) /\
    memacc_exp h e s1
  else exists a, (s1' = s1 /\ x1 = Some (Exit a)).
Proof.
  intros. inversion XS; subst. destruct (exp_known e) eqn:K.
    split.
      split. reflexivity.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      simpl in E. rewrite <- E. reflexivity.

      eapply memacc_exp_true. exact K. exact E.

    exists a. split; reflexivity.
Qed.

Lemma reduce_if:
  forall x1 h s1 e q1 q2 s1' (XS: exec_stmt h s1 (If e q1 q2) s1' x1),
  if exp_known e then
    (exec_stmt h s1 (match feval_exp e s1 with VaU _ _ c _ => if c then q2 else q1 end) s1' x1) /\
    memacc_exp h e s1
  else
    exists (c:N), exec_stmt h s1 (if c then q2 else q1) s1' x1.
Proof.
  intros. inversion XS; subst. destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      rewrite <- E. simpl. destruct c; assumption.

      eapply memacc_exp_true. exact K. exact E.

    eexists. exact XS0.
Qed.


(* Using the functional interpreter, we now define a set of tactics that reduce expressions to values,
   and statements to stores & exits.  These tactics are carefully implemented to avoid simplifying
   anything other than the machinery of the functional interpreter, so that Coq does not spin out of
   control attempting to execute the entire program.  Our objective is to infer a reasonably small,
   well-formed symbolic expression that captures the result of executing each assembly instruction.
   This result can be further reduced by the user (e.g., using "simpl") if desired.  Call-by-value
   strategy is used here, since our goal is usually to reduce as much as possible of the target
   expression, which might include arguments of an enclosing unexpandable function. *)

Declare Reduction simpl_exp :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ].

Ltac simpl_exp :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ];
  repeat match goal with |- context [ bits_of_mem ?w ] =>
    let b := eval compute in (bits_of_mem w) in change (bits_of_mem w) with b
  end.

Tactic Notation "simpl_exp" "in" hyp(H) :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ] in H;
  repeat match type of H with context [ bits_of_mem ?w ] =>
    let b := eval compute in (bits_of_mem w) in change (bits_of_mem w) with b in H
  end.


(* Statement simplification most often gets stuck at variable-reads, since the full content of the
   store is generally not known (s is a symbolic expression).  We can often push past this obstacle
   by applying the update_updated and update_frame theorems to automatically infer that the values
   of variables not being read are irrelevant.  The "simpl_stores" tactic does so. *)

Remark if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.
Proof. intros. destruct n; reflexivity. Qed.

Ltac simpl_stores :=
  repeat first [ rewrite update_updated | rewrite update_frame; [|discriminate 1] ];
  repeat rewrite if_N_same;
  repeat match goal with |- context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Tactic Notation "simpl_stores" "in" hyp(H) :=
  repeat first [ rewrite update_updated in H | rewrite update_frame in H; [|discriminate 1] ];
  repeat rewrite if_N_same in H;
  repeat match type of H with context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) in H by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.


(* To facilitate expression simplification, it is often convenient to first consolidate all information
   about known variable values into the expression to be simplified.  The "stock_store" tactic searches the
   proof context for hypotheses of the form "s var = value", where "var" is some variable appearing in the
   expression to be reduced and "s" is the store, and adds "s[var:=value]" to the expression. *)

Ltac stock_store :=
  lazymatch goal with |- exec_stmt _ _ ?Q _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch goal with |- exec_stmt _ ?S _ _ _ =>
        lazymatch S with context [ update _ V _ ] => fail | _ =>
          erewrite (store_upd_eq S V) by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Goal is not of the form (exec_stmt ...)"
  end.

Tactic Notation "stock_store" "in" hyp(XS) :=
  lazymatch type of XS with exec_stmt _ _ ?Q _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch type of XS with exec_stmt _ ?S _ _ _ =>
        lazymatch S with context [ update _ V _ ] => fail | _ =>
          erewrite (store_upd_eq S V) in XS by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* Replace any unresolved variable lookups as fresh Coq variables after functional evaluation. *)

Ltac destr_ugets H :=
  try (rewrite fold_uget in H; repeat rewrite fold_uget in H;
       repeat match type of H with context [ uget ?X ] =>
         let UGET := fresh "UGET" in
         let utyp := fresh "utyp" in let mem := fresh "mem" in let n := fresh "n" in let w := fresh "w" in
         destruct (uget X) as [utyp mem n w] eqn:UGET
       end).

(* As the functional interpreter interprets stmts within a sequence, it infers memory access
   hypotheses as a side-effect of interpreting Load and Store expressions.  It splits these
   off into separate hypotheses in order to continue stepping the main exec_stmt hypothesis.
   Many are redundant (e.g., because Load or Store is applied to the same expression multiple
   times within the stmt), so we automatically clear any redundant ones. *)

Ltac nomemaccs T :=
  lazymatch T with NoMemAcc => idtac
  | if _ then ?E1 else ?E2 => nomemaccs E1; nomemaccs E2
  | ?E1 /\ ?E2 => nomemaccs E1; nomemaccs E2
  | _ => fail
  end.

Ltac destruct_memacc H :=
  lazymatch type of H with
  | _=_ /\ _=_ => idtac
  | exists _, _ => let u := fresh "u" in destruct H as [u H]; simpl_exp in H; simpl_stores in H
  | ?H1 /\ ?H1 =>
    lazymatch goal with
    | [ _:H1 |- _ ] => clear H
    | _ => apply proj1 in H; destruct_memacc H
    end
  | ?H1 /\ ?H2 =>
    lazymatch goal with
    | [ _:H1, _:H2 |- _ ] => clear H
    | [ _:H1 |- _ ] => apply proj2 in H; destruct_memacc H
    | [ _:H2 |- _ ] => apply proj1 in H; destruct_memacc H
    | _ => let H' := fresh "ACC" in destruct H as [H H']; destruct_memacc H; destruct_memacc H'
    end
  | ?T => try (nomemaccs T; clear H)
  end.

(* Finally, simplifying a hypothesis of the form (exec_stmt ...) entails applying the functional
   interpreter to each statement in the sequence (usually a Move), using simpl_stores to try to
   infer any unresolved variable-reads, using destr_ugets to abstract any unresolved store-reads,
   and repeating this until we reach a conditional or the end of the sequence.  (We don't attempt
   to break conditionals into cases automatically here, since often the caller wants to decide
   which case distinction is best.)

   Here, parameter "tac" is a caller-supplied tactic (taking a hypothesis as its argument) which
   is applied to simplify the expression after each step within a stmt.  This is most often useful
   for simplifying memory access hypotheses before they get split off from the main hypothesis. *)

Ltac finish_simpl_stmt tac H :=
  simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H; tac H; destruct_memacc H.

Ltac simpl_stmt_loop tac H :=
  lazymatch type of H with exec_stmt _ _ ?q _ _ => lazymatch q with
  | Seq (Move _ _) _ =>
    apply reduce_seq_move in H; finish_simpl_stmt tac H; simpl_stmt_loop tac H
  | Nop => apply reduce_nop in H; unfold cast in H
  | Move _ _ => apply reduce_move in H; finish_simpl_stmt tac H
  | Jmp _ => apply reduce_jmp in H; finish_simpl_stmt tac H
  | If _ _ _ => apply reduce_if in H;
      simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H;
      lazymatch type of H with
      | exists _, _ => let c := fresh "c" in
          destruct H as [c H]; simpl_exp in H; simpl_stores in H; destr_ugets H
      | _ => tac H; destruct_memacc H
      end
  | _ => first
  [ apply reduce_seq_move in H; finish_simpl_stmt tac H; simpl_stmt_loop tac H
  | apply reduce_nop in H; unfold cast in H
  | apply reduce_move in H; finish_simpl_stmt tac H
  | apply reduce_jmp in H; finish_simpl_stmt tac H
  | apply reduce_if in H;
      simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H;
      lazymatch type of H with
      | exists _, _ => let c := fresh "c" in
          destruct H as [c H]; simpl_exp in H; simpl_stores in H; destr_ugets H
      | _ => tac H; destruct_memacc H
      end ]
  end end.

Tactic Notation "simpl_stmt" "using" tactic(tac) "in" hyp(H) :=
  lazymatch type of H with exec_stmt _ _ _ _ ?x => simpl_stmt_loop tac H
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* Combining all of the above, our most typical simplification regimen first stocks the store
   of the exec_stmt with any known variable values from the context, then applies the functional
   interpreter, and then unfolds a few basic constants. *)

Tactic Notation "psimpl" "using" tactic(tac) "in" hyp(H) :=
  stock_store in H; simpl_stmt using tac in H; unfold tobit in H.

End PICINAE_FINTERP.


Module PicinaeFInterp (IL: PICINAE_IL) <: PICINAE_FINTERP IL.
  Include PICINAE_FINTERP IL.
End PicinaeFInterp.
