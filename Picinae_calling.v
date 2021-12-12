 (* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2021 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Calling convention preservation and tracing         MMMMMMMMMMMMMMMMM^NZMMN+Z
   * traces states in all program executions            MMMMMMMMMMMMMMM/.$MZM8O+
   * static assertions of preserved states               MMMMMMMMMMMMMM7..$MNDM+
     throughout program execution                         MMDMMMMMMMMMZ7..$DM$77
   * correctness/soundness of these static assertions      MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
                                                             MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
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

Require Import Picinae_theory.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Import Utf8.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Etacs.
Require Import Ntree.
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

(* Functional interpretation of expressions and statements entails instantiating
   a functor that accepts the architecture-specific IL syntax and semantics. *)
Module Type PICINAE_CALLING_DEFS (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL).
Import IL.
Import TIL.

(* Some equality definitions *)
Program Instance endian_EqDec: EqDec endianness.
Next Obligation. Proof. decide equality. Defined.

Program Instance binop_EqDec: EqDec binop_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance unop_EqDec: EqDec unop_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance cast_EqDec: EqDec cast_typ.
Next Obligation. Proof. decide equality. Defined.

Program Instance bool_EqDec : EqDec bool.
Next Obligation. Proof. decide equality. Defined.

Program Instance option_EqDec A `(EA : EqDec A) : EqDec (option A).
Next Obligation. Proof. decide equality. apply iseq. Defined.

Program Instance tuple_EqDec A B `(EA : EqDec A) `(EA : EqDec B): EqDec (A * B).
Next Obligation. Proof. decide equality; apply iseq. Defined.

Program Instance list_EqDec A `(EA : EqDec A) : EqDec (list A).
Next Obligation. Proof. decide equality. apply iseq. Defined.

Program Instance exp_EqDec: EqDec exp.
Next Obligation. Proof. decide equality; apply iseq. Defined.

(* We define a store delta as a variable to partial mapping onto
 * some expression. This is partial to account for "undefined" variables (which
 * could also be undefined "memory" variables) *)
Definition store_delta := list (var * option exp).

(* Convert a list of variables and their values to a store function. *)
Fixpoint delta_updlst s (l: store_delta) : var ⇀ exp :=
  match l with nil => s | (v,e)::t => update (delta_updlst s t) v e end.

(* Remove a variable from a list of variables and their values. *)
Fixpoint remlst v (l: store_delta) : store_delta :=
  match l with
  | nil => nil
  | (v',u)::t => if v == v' then remlst v t else (v',u)::(remlst v t)
  end.

Definition setlst (l: store_delta) v e: store_delta := (v, e) :: remlst v l.
Notation "f [[ x := y ]]" := (setlst f x y) (at level 50, left associativity).

Definition vdomain := var -> bool.
Definition init_delta (domain: vdomain): var ⇀ exp := fun v =>
  if domain v then Some (Var v) else None.
Notation "f <{ domain }> [[ x ]]" :=
  (delta_updlst (init_delta domain) f x)
  (at level 50, left associativity).

Definition trim_delta_state (vd: vdomain) (δ: store_delta) :=
  flat_map (fun '(v, e) => if vd v then (v, e) :: nil else nil) δ.

Definition has_delta (vd: vdomain) (h: hdomain) (s0 s: store) (δ: store_delta) :=
  forall v e val (LUv: δ<{vd}>[[v]] = Some e) (EE: eval_exp h s0 e val), s v = val.

Definition delta_nounk (vd: vdomain) (δ: store_delta) :=
  forall v e (LUv: δ<{vd}>[[v]] = Some e), forall_exps_in_exp not_unknown e.

Definition delta_defined (δ: store_delta) :=
  map fst δ.

Definition delta_equivb (vd: vdomain) (δ1 δ2: store_delta) :=
  forallb (fun '(v, _) => iseqb (δ1<{vd}>[[v]]) (δ2<{vd}>[[v]])) (δ1 ++ δ2).

Definition delta_equiv (vd: vdomain) (δ1 δ2: store_delta) :=
  forall v, δ1<{vd}>[[v]] = δ2<{vd}>[[v]].

Definition delta_same_domain (vd: vdomain) (δ1 δ2: store_delta) :=
  forall v, match (δ1<{vd}>[[v]]), (δ2<{vd}>[[v]]) with
            | Some _, Some _ => True
            | None, None => True
            | _, _ => False
            end.

Fixpoint simplify_exp_eval e: option (N * bitwidth) :=
  match e with
  | Var v => None
  | Word n w => Some (n, w)
  | Load _ _ _ _ => None
  | Store _ _ _ _ _ => None
  | BinOp op e1 e2 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (n1, w1) =>
          match simplify_exp_eval e2 with
          | Some (n2, w2) =>
              if w1 == w2 then
                match eval_binop op w1 n1 n2 with
                | VaN n w => Some (n, w)
                | _ => None
                end
              else None
          | None => None
          end
      end
  | UnOp op e1 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (n1, w1) =>
          match eval_unop op n1 w1 with
          | VaN n w => Some (n, w)
          | _ => None
          end
      end
  | Cast op w' e1 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (n1, w1) => Some (cast op w1 w' n1, w')
      end
  | Let _ _ _ => None
  | Ite e1 e2 e3 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (0, _) => simplify_exp_eval e3
      | Some (N.pos _, _) => simplify_exp_eval e2
      end
  | Extract n1 n2 e1 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (n, w) => Some (xbits n n2 (N.succ n1), N.succ n1 - n2)
      end
  | Concat e1 e2 =>
      match simplify_exp_eval e1 with
      | None => None
      | Some (n1, w1) =>
          match simplify_exp_eval e2 with
          | None => None
          | Some (n2, w2) => Some (N.lor (N.shiftl n1 w2) n2, w1 + w2)
          end
      end
  | Unknown _ => None
  end.

Inductive SimpExp :=
  | SWord (n: N) (w: bitwidth)
  | SExp (e: exp)
  | SExpOff (e: exp) (n: N) (w: bitwidth).

Inductive hastyp_se (c: typctx): SimpExp -> typ -> Prop :=
  | SE_SWord (n: N) (w: bitwidth) (LT: n < 2 ^ w):
      hastyp_se c (SWord n w) (NumT w)
  | SE_SExp (e: exp) (t: typ) (TE: hastyp_exp c e t): hastyp_se c (SExp e) t
  | SE_SExpOff (e: exp) (n: N) (w: bitwidth) (TE: hastyp_exp c e (NumT w))
      (LT: n < 2 ^ w): hastyp_se c (SExpOff e n w) (NumT w).

Theorem hastyp_se_deterministic: forall c se t1 t2
  (TSE1: hastyp_se c se t1) (TSE2: hastyp_se c se t2), t1 = t2.
Proof.
  intros. destruct se; inversion TSE1; inversion TSE2; try reflexivity.
  subst. einstantiate hastyp_exp_unique. apply hub_refl.
  apply TE. apply TE0. assumption.
Qed.

Definition se_to_exp se :=
  match se with
  | SWord n w => Word n w
  | SExp e => e
  | SExpOff e n w => BinOp OP_PLUS e (Word n w)
  end.

Definition eval_binop_num bop w n1 n2 :=
  match eval_binop bop w n1 n2 with
  | VaN n _ => n
  | _ => 0 (* should *never* happen *)
  end.

Definition se_eval_binop (flipped: bool) w op n1 e n2 :=
  let def :=
    if flipped then
      SExp (BinOp op (se_to_exp (SExpOff e n2 w)) (se_to_exp (SWord n1 w)))
    else
      SExp (BinOp op (se_to_exp (SWord n1 w)) (se_to_exp (SExpOff e n2 w))) in
  match op with
  | OP_PLUS => SExpOff e ((n2 + n1) mod 2^w) w
  | OP_MINUS =>
      if flipped then SExpOff e ((n2 + 2^w - n1) mod 2^w) w
      else def
  | _ => def
  end.

Fixpoint simplify_exp_arith0 c e :=
  match simplify_exp_eval e with
  | Some (n, w) => SWord n w
  | None =>
      match e with
      | Var _ => SExp e
      | Word n w => SWord n w
      | Load e1 e2 en w =>
          let e1' := se_to_exp (simplify_exp_arith0 c e1) in
          let e2' := se_to_exp (simplify_exp_arith0 c e2) in
          SExp (Load e1' e2' en w)
      | Store e1 e2 e3 en w =>
          let e1' := se_to_exp (simplify_exp_arith0 c e1) in
          let e2' := se_to_exp (simplify_exp_arith0 c e2) in
          let e3' := se_to_exp (simplify_exp_arith0 c e3) in
          SExp (Store e1' e2' e3' en w)
      | BinOp bop e1 e2 =>
          let se1 := simplify_exp_arith0 c e1 in
          let se2 := simplify_exp_arith0 c e2 in
          match se1, se2 with
          | SExp e, SWord n2 w => se_eval_binop true w bop n2 e 0
          | SWord n1 w, SExp e  => se_eval_binop false w bop n1 e 0
          | SExpOff e n1 _, SWord n2 w => se_eval_binop true w bop n2 e n1
          | SWord n1 w, SExpOff e n2 _  => se_eval_binop false w bop n1 e n2
          | _, _ => SExp (BinOp bop (se_to_exp se1) (se_to_exp se2))
          end
      | UnOp uop e1 =>
          SExp (UnOp uop (se_to_exp (simplify_exp_arith0 c e1)))
      | Cast op w' e =>
          let se := simplify_exp_arith0 c e in
          match typchk_exp e c with
          | Some (NumT w) =>
              if w' == w then se
              else SExp (Cast op w' (se_to_exp se))
          | _ => SExp (Cast op w' (se_to_exp se))
          end
      | Let v e1 e2 =>
          let e1' := se_to_exp (simplify_exp_arith0 c e1) in
          match typchk_exp e1' c with
          | Some t =>
              let e2' := se_to_exp (simplify_exp_arith0 (c [v := Some t]) e2) in
              SExp (Let v e1' e2')
          | None => SExp e
          end
      | Unknown _ => SExp e
      | Ite e1 e2 e3 =>
          let e1' := se_to_exp (simplify_exp_arith0 c e1) in
          let e2' := se_to_exp (simplify_exp_arith0 c e2) in
          let e3' := se_to_exp (simplify_exp_arith0 c e3) in
          SExp (Ite e1' e2' e3')
      | Extract n1 n2 e1 =>
          SExp (Extract n1 n2 (se_to_exp (simplify_exp_arith0 c e1)))
      | Concat e1 e2 =>
          let e1' := se_to_exp (simplify_exp_arith0 c e1) in
          let e2' := se_to_exp (simplify_exp_arith0 c e2) in
          SExp (Concat e1' e2')
      end
  end.

Definition simplify_exp_arith c e := se_to_exp (simplify_exp_arith0 c e).

Fixpoint subst_valid (vd: vdomain) (δ: store_delta) e: bool :=
  match e with
  | Var v =>
      match δ<{vd}>[[v]] with
      | Some e => true
      | None => false
      end
  | Word _ _ => true
  | Load e1 e2 _ _ => subst_valid vd δ e1 && subst_valid vd δ e2
  | Store e1 e2 e3 _ _ => subst_valid vd δ e1 && subst_valid vd δ e2 && subst_valid vd δ e3
  | BinOp _ e1 e2 => subst_valid vd δ e1 && subst_valid vd δ e2
  | UnOp _ e => subst_valid vd δ e
  | Cast _ _ e => subst_valid vd δ e
  | Let v e e_in =>
      if subst_valid vd δ e
      then subst_valid vd (δ[[v := (Some (Word 0 0))]]) e_in
      else subst_valid vd (δ[[v := None]]) e_in
  | Unknown _ => false
  | Ite e1 e2 e3 => subst_valid vd δ e1 && subst_valid vd δ e2 && subst_valid vd δ e3
  | Extract _ _ e => subst_valid vd δ e
  | Concat e1 e2 => subst_valid vd δ e1 && subst_valid vd δ e2
  end.

Fixpoint subst_exp0 (vd: vdomain) (δ: store_delta) e: exp :=
  match e with
  | Var v =>
      match δ<{vd}>[[v]] with
      | Some e => e
      | None => Unknown 0 (* Note we should return error in subst_err here *)
      end
  | Word _ _ => e
  | Load e1 e2 en len => Load (subst_exp0 vd δ e1) (subst_exp0 vd δ e2) en len
  | Store e1 e2 e3 en len => Store (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
      (subst_exp0 vd δ e3) en len
  | BinOp op e1 e2 => BinOp op (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
  | UnOp op e => UnOp op (subst_exp0 vd δ e)
  | Cast typ w' e => Cast typ w' (subst_exp0 vd δ e)
  | Let v e e_in =>
      if subst_valid vd δ e
      then subst_exp0 vd (δ[[v := (Some (subst_exp0 vd δ e))]]) e_in
      else subst_exp0 vd (δ[[v := None]]) e_in
  | Unknown _ => e
  | Ite e1 e2 e3 => Ite (subst_exp0 vd δ e1) (subst_exp0 vd δ e2) (subst_exp0 vd δ e3)
  | Extract n1 n2 e => Extract n1 n2 (subst_exp0 vd δ e)
  | Concat e1 e2 => Concat (subst_exp0 vd δ e1) (subst_exp0 vd δ e2)
  end.

Definition subst_exp (vd: vdomain) (δ: store_delta) e: option exp :=
  if subst_valid vd δ e then Some (subst_exp0 vd δ e) else None.

Definition trace_states := treeN store_delta.

Definition init_ts a0: trace_states :=
  tupdate_n treeN_nil a0 nil.

Inductive jump_target: Set :=
  | jump_addr (a: addr)
  | jump_symbolic. (* a call or return *)

Inductive eval_jump (p: program) (s: store):
  addr -> jump_target -> Prop :=
  | EJ_jump_addr (a: addr): eval_jump p s a (jump_addr a)
  | EJ_jump_symbolic (a: addr) (LU: p s a = None):
      eval_jump p s a jump_symbolic.

Definition eval_jump_targets p s a (jmps: list jump_target): Prop :=
  Exists (eval_jump p s a) jmps.

Inductive ts_evidence :=
  | has_jump_targets (a1: addr) (q0: stmt) (δ: store_delta) (vd: vdomain)
      (e: exp) (jmps: list jump_target).

Inductive ts_evidence_proved (p: program) (h: hdomain)
  (a0: addr) (s0: store): ts_evidence -> Prop :=
  | EV_has_jump_targets (a1: addr) (q0: stmt) (δ: store_delta)
      (vd: vdomain) (e: exp) (jmps: list jump_target) (EJT: forall n a' s0' s1
        (XP: exec_prog h p a0 s0 n s0' (Exit a1))
        (XS0: exec_stmt h s0' q0 s1 None)
        (XS: exec_stmt h s1 (Jmp e) s1 (Some (Exit a')))
        (HD: has_delta vd h s0 s1 δ),
        eval_jump_targets p s1 a' jmps):
        ts_evidence_proved p h a0 s0 (has_jump_targets a1 q0 δ vd e jmps).

Definition trace_state_res :=
  option (list (store_delta * option exit) * list ts_evidence).

Definition sat_evidences (evs: list ts_evidence) p h a0 s0 :=
  Forall (ts_evidence_proved p h a0 s0) evs.

(* TODO: remove redundant ts_evidences *)
Definition app_evidences (ev1 ev2: list ts_evidence) := ev1 ++ ev2.
Notation "ev1 !++ ev2" := (app_evidences ev1 ev2) (at level 60, right associativity).

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

Definition jump_hint := addr -> store_delta -> exp -> option (list jump_target).

Fixpoint simple_trace_stmt0 (hint: jump_hint) (vd: vdomain) (δ: store_delta)
  (a: addr) (q0: stmt) (q: stmt) (c: typctx): trace_state_res :=
  match q with
  | Nop => Some ((δ, None) :: nil, nil)
  | Move v e =>
      let exp :=
        match subst_exp vd δ e with
        | Some e' => Some (simplify_exp_arith c e')
        | None => None
        end in
      Some ((δ[[v := exp]], None) :: nil, nil)
  | Jmp e =>
      match hint a δ e with
      | Some jmps =>
          Some (flat_map (fun j =>
            match j with
            | jump_addr a => ((δ, Some (Exit a)) :: nil)
            | jump_symbolic => nil
            end) jmps, has_jump_targets a q0 δ vd e jmps :: nil)
      | None =>
          match subst_exp vd δ e with
          | Some (Word n _) => Some ((δ, Some (Exit n)) :: nil, nil)
          | _ => None
          end
      end
  | Exn n => Some ((δ, Some (Raise n)) :: nil, nil)
  | Seq q1 q2 =>
      match simple_trace_stmt0 hint vd δ a q0 q1 c with
      | None => None
      | Some (paths1, ev1) =>
          let res := map_option (fun '(δ', x) =>
            match x with
            | None =>
                match simple_trace_stmt0 hint vd δ' a (Seq q0 q1) q2 c with
                | None => None
                | Some (paths2, _) => Some paths2
                end
            | Some _ => Some ((δ', x) :: nil)
            end) paths1 in
          let ev' := flat_map (fun '(δ', x) =>
            match x with
            | None =>
                match simple_trace_stmt0 hint vd δ' a (Seq q0 q1) q2 c with
                | None => nil
                | Some (_, ev2) => ev2
                end
            | Some _ => nil
            end) paths1 !++ ev1 in
          match res with
          | None => None
          | Some ll => Some (concat ll, ev')
          end
      end
  | If _ q1 q2 =>
      match simple_trace_stmt0 hint vd δ a q0 q1 c,
            simple_trace_stmt0 hint vd δ a q0 q2 c with
      | None, _ | _, None => None
      | Some (paths1, ev1), Some (paths2, ev2) =>
          Some (paths1 ++ paths2, ev1 !++ ev2)
      end
  | Rep _ s => None
  end.

Definition simple_trace_stmt (hint: jump_hint) (vd: vdomain) (δ: store_delta)
  (a: addr) (q: stmt) (c: typctx): trace_state_res :=
  match simple_trace_stmt0 hint vd δ a Nop q c with
  | Some (next_states, evs) =>
      Some (map (fun '(δ, x) => (trim_delta_state vd δ, x)) next_states, evs)
  | None => None
  end.

Definition delta_join (vd: vdomain) (δ1 δ2: store_delta): store_delta :=
  fold_right (fun v δ' =>
    δ'[[v := if δ1<{vd}>[[v]] == δ2<{vd}>[[v]] then δ2<{vd}>[[v]] else None]])
  nil (delta_defined (δ1 ++ δ2)).

Definition join_states_if_changed (vd: vdomain) (δ1: option store_delta)
  (δ2: store_delta): option store_delta :=
  match δ1 with
  | Some δ1 =>
      if delta_equivb vd δ1 δ2
      then None
      else let δ_merge := delta_join vd δ1 δ2 in
        if delta_equivb vd δ1 δ_merge then
            None
        else
            Some δ_merge
  | None => Some δ2
  end.

Definition null_state: store := fun _ => VaN 0 0.

Definition process_state (vd: vdomain) (exitof: option exit -> exit)
  (st: store_delta * option exit) (accum: trace_states * bool) :=
  let '(ts, changed) := accum in
  let '(δ', x) := st in
  (* If this exited to an address, update state on that address
   * Otherwise if it is a raise, we don't actually care about
   * what state we end up in (nothing to merge with), since
   * there is no way for us to return back later on to a valid
   * address. *)
  match exitof x with
  | Exit next_addr =>
      (* Check if joining states changed something. If so, we update and mark
       * this as changed *)
      match join_states_if_changed vd (tget_n ts next_addr) δ' with
      | Some δ_merge => (tupdate_n ts next_addr δ_merge, true)
      | None => (ts, changed)
      end
  | Raise _ => (ts, changed)
  end.

Definition stmt_correct vd q δ x := forall s0 h s s' (XS: exec_stmt h s q s' x),
  has_delta vd h s0 s' δ.

Definition correct_trace_sub_prog vd p ts h a0 s0 :=
  (forall a1 s1 n1 sz' q'
    (XP: exec_prog h (sub_prog p (tkeys_n ts)) a0 s0 n1 s1 (Exit a1))
    (LU': p s1 a1 = Some (sz', q')),
    exists δ, tget_n ts a1 = Some δ /\ has_delta vd h s0 s1 δ).

Definition correct_trace_prog vd p ts h a0 s0 :=
  (forall a1 s1 n1 sz' q'
    (XP: exec_prog h p a0 s0 n1 s1 (Exit a1))
    (LU': p s1 a1 = Some (sz', q')),
    exists δ, tget_n ts a1 = Some δ /\ has_delta vd h s0 s1 δ).

Definition trace_program_step_at (vd: vdomain) (c: typctx) (p: program)
  (hints: jump_hint) addr (accum: option (trace_states * bool * list ts_evidence)) :=
  match accum with
  | None => None
  | Some (ts, changed, old_evs) =>
      (* If this is a proper address in program, process that. Otherwise, this
       * is an invalid execution, so wouldn't happen to begin with. *)
      match p null_state addr with
      | None => Some (ts, changed, old_evs)
      | Some (sz, q) =>
          (* We have to had visited this address to begin with; otherwise, we
           * won't be able to push trace states for this address's successors. *)
          match tget_n ts addr with
          | None => Some (ts, changed, old_evs)
          | Some δ_a =>
              match simple_trace_stmt hints vd δ_a addr q c with
              | None => None
              | Some (next_states, evs) =>
                  let res := fold_right (process_state vd
                    (exitof (addr + sz))) (ts, changed) next_states in
                  Some (res, evs !++ old_evs)
              end
          end
      end
  end.

Definition expand_trace_program (vd: vdomain) (c: typctx) (p: program)
  (hints: jump_hint) (init_ts: trace_states):
  option (trace_states * bool * list ts_evidence) :=
  fold_right (trace_program_step_at vd c p hints) (Some (init_ts, false, nil))
    (tkeys_n init_ts).

Definition iterM (n: N) {A} (f: A -> option A) (x: A) :=
  N.iter n (fun x => match x with Some x => f x | None => None end) (Some x).

Definition expand_trace_program_n (n: N) (vd: vdomain) (c: typctx)
  (hints: jump_hint) (p: program) (init_ts: trace_states):
  option (trace_states * bool * list ts_evidence) :=
  N.iter n (fun x =>
    match x with
    | Some (ts, true, _) => expand_trace_program vd c p hints ts
    | Some (ts, false, ev) => Some (ts, false, ev)
    | None => None
    end) (Some (init_ts, true, nil)).

Definition compute_trace_program_n n vd c hints p ts :=
  match expand_trace_program_n n vd c hints p ts with
  | Some (ts, _, _) => ts
  | None => ts
  end.

Definition check_trace_states (vd: vdomain) (c: typctx) (hints: jump_hint)
  (p: program) (ts: trace_states) (a0: addr): option (list ts_evidence) :=
  match p null_state a0 with
  | None => None
  | Some _ =>
      match tget_n ts a0 with
      | None => None
      | Some δ =>
          if forallb (fun '(v, e) =>
              match e with
              | None => true
              | Some e => iseqb e (Var v)
              end) δ
          then match expand_trace_program vd c p hints ts with
               | None => None
               | Some (_, true, _) => None
               | Some (_, false, ev) => Some ev
               end
          else None
      end
  end.

End PICINAE_CALLING_DEFS.

Module Type PICINAE_CALLING (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL).
Import IL.
Import TIL.
Include PICINAE_CALLING_DEFS IL TIL.

Module FInterp := PicinaeFInterp IL TIL.

Ltac concretize_delta HD v :=
  lazymatch type of HD with has_delta ?vd ?h ?s0 ?s1 ?δ =>
  lazymatch eval compute in (δ<{vd}>[[v]]) with
  | Some ?e =>
      let EE := fresh in
      FInterp.mk_eval_exp h s0 e EE; [|
          let SV := fresh "Hsv" in
          einstantiate trivial (HD v) as SV; clear EE]
  | None => fail "Unknown value for " v
  end
  end.

Parameter checked_trace_program_steady_correct:
  forall vd c p hints ts h a0 s0 evs
  (NWC: forall sa sb a, p sa a = p sb a)
  (CHK: check_trace_states vd c hints p ts a0 = Some evs)
  (SAT: sat_evidences evs p h a0 s0),
  correct_trace_prog vd p ts h a0 s0.

End PICINAE_CALLING.

Module PicinaeCalling (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL): PICINAE_CALLING IL TIL.

Import IL.
Import TIL.

Module PTheory := PicinaeTheory IL.
Import PTheory.

Module FInterp := PicinaeFInterp IL TIL.
Import FInterp.

Include PICINAE_CALLING_DEFS IL TIL.

Theorem delta_updlst_def: forall f δ v (ND: ~(In v (delta_defined δ))),
  delta_updlst f δ v = f v.
Proof.
  induction δ; intros.
  - reflexivity.
  - simpl. destruct a as [v' e']. rewrite update_frame. apply IHδ.
    intros Contra. apply ND. right. assumption.
    intro. subst. apply ND. left. reflexivity.
Qed.

Theorem delta_remlst_removed: forall δ fn v,
  delta_updlst fn (remlst v δ) v = fn v.
Proof.
  intros. apply delta_updlst_def. intros Contra. revert v Contra. induction δ; intros.
  - inversion Contra.
  - simpl in Contra. destruct a as [v' u']. eapply IHδ. destruct (v == v').
    eassumption. apply neq_sym in n. destruct Contra; [contradiction n|assumption].
Qed.

Theorem delta_remlst_frame: forall δ fn x z (NEQ: z ≠ x),
  delta_updlst fn (remlst x δ) z = delta_updlst fn δ z.
Proof.
  induction δ; intros.
  - reflexivity.
  - simpl. destruct a as [v' e']. destruct (z == v').
    + subst. apply neq_sym in NEQ. vantisym x v' by assumption. simpl.
      repeat rewrite update_updated. reflexivity.
    + simpl. rewrite update_frame by assumption. destruct (x == v').
      apply IHδ. assumption. simpl. rewrite update_frame by assumption.
      apply IHδ. assumption.
Qed.

Theorem delta_update_updated: forall fn δ x y, delta_updlst fn (δ [[x := y]]) x = y.
Proof. intros. unfold setlst. simpl. apply update_updated. Qed.

Theorem delta_update_frame: forall δ fn x y z (NEQ: z ≠ x),
  delta_updlst fn (δ [[x := y]]) z = delta_updlst fn δ z.
Proof.
  intros. unfold setlst. simpl. rewrite update_frame by assumption.
  apply delta_remlst_frame. assumption.
Qed.

Theorem delta_delta_updlst_iff_defined: forall f δ v,
  In v (delta_defined δ) <-> In (v, delta_updlst f δ v) δ.
Proof.
  split.
  - intro InDef. revert_all. induction δ; intros.
    + inversion InDef.
    + simpl in *. destruct a as [v' e']. destruct (v == v').
      * subst. left. rewrite update_updated. reflexivity.
      * destruct InDef. subst. contradiction n. reflexivity. right.
        rewrite update_frame by assumption. apply IHδ; assumption.
  - intro InDelta. revert_all. induction δ; intros.
    + inversion InDelta.
    + destruct a as [v' e']. destruct (v == v'); subst; simpl in *.
      * left. reflexivity.
      * destruct InDelta. inversion H. subst. contradict n. reflexivity.
        right. apply IHδ. rewrite update_frame in H; assumption.
Qed.

Corollary delta_delta_updlst_iff_defined_contra: forall f δ v,
  ~ In v (delta_defined δ) <-> ~ In (v, delta_updlst f δ v) δ.
Proof. intros. contrapositive delta_delta_updlst_iff_defined. Qed.

Corollary delta_updlst_cases: forall f δ v,
  (In (v, delta_updlst f δ v) δ) \/ delta_updlst f δ v = f v.
Proof.
  intros. edestruct (@in_dec var iseq).
  - rewrite delta_delta_updlst_iff_defined in i. left. eassumption.
  - right. apply delta_updlst_def. assumption.
Qed.

Theorem delta_equivb_iff_delta_equiv: forall vd δ1 δ2,
  delta_equivb vd δ1 δ2 = true <-> delta_equiv vd δ1 δ2.
Proof.
  unfold delta_equiv, delta_equivb. split; intro EQV.
  - (* -> *) intro. rewrite forallb_app, andb_true_iff in EQV.
    destruct EQV as [EQV1 EQV2]. edestruct (in_dec iseq (v, δ1<{vd}>[[v]])).
    + eapply forallb_forall in EQV1; [|eassumption]. simpl in EQV1.
      unfold iseqb in EQV1. destruct (_ == _); try discriminate. assumption.
    + edestruct (in_dec iseq (v, δ2<{vd}>[[v]])).
      * eapply forallb_forall in EQV2; [|eassumption]. simpl in EQV2.
        unfold iseqb in EQV2. destruct (_ == _); try discriminate. assumption.
      * repeat rewrite delta_updlst_def; try rewrite delta_delta_updlst_iff_defined_contra;
        trivial2.
  - (* <- *) rewrite forallb_forall. intros. destruct x as [v e]. rewrite EQV.
    unfold iseqb. vreflexivity (δ2<{vd}>[[v]]). reflexivity.
Qed.

Corollary delta_equivb_iff_delta_equiv_contra: forall vd δ1 δ2,
  delta_equivb vd δ1 δ2 = false <-> ~ delta_equiv vd δ1 δ2.
Proof.
  intros. rewrite <- not_true_iff_false.
  contrapositive delta_equivb_iff_delta_equiv.
Qed.

Lemma delta_equiv_has_delta: forall δ1 δ2 vd h s0 s
  (EQ: delta_equiv vd δ1 δ2) (HD: has_delta vd h s0 s δ1),
  has_delta vd h s0 s δ2.
Proof.
  unfold has_delta, delta_equiv. intros. eapply HD; try rewrite EQ; eassumption.
Qed.

Lemma delta_equiv_refl: forall vd δ1, delta_equiv vd δ1 δ1.
Proof. unfold delta_equiv. reflexivity. Qed.

Lemma delta_equiv_symm: forall vd δ1 δ2,
  delta_equiv vd δ1 δ2 <-> delta_equiv vd δ2 δ1.
Proof. unfold delta_equiv. split; intros; rewrite H; reflexivity. Qed.

Lemma delta_defined_app: forall δ1 δ2,
  delta_defined (δ1 ++ δ2) = delta_defined δ1 ++ delta_defined δ2.
Proof. intros. unfold delta_defined. apply map_app. Qed.

Lemma not_or: forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  split; intros.
  - split; contradict H; (left + right); apply H.
  - intros Contra. destruct H as [HA HB]. destruct Contra as [X|X];
    (apply HA + apply HB); apply X.
Qed.

Lemma not_in_app: forall A (a: A) l1 l2,
  ~(In a (l1 ++ l2)) <-> ~(In a l1) /\ ~(In a l2).
Proof. intros. rewrite <- not_or. contrapositive in_app_iff. Qed.

Lemma trim_delta_state_preserve: forall vd δ v
  (VD: vd v = true), trim_delta_state vd δ <{vd}>[[v]] = δ<{vd}>[[v]].
Proof.
  induction δ; intros.
  - reflexivity.
  - destruct a as [v' e']. simpl. destruct (v == v').
    + subst. rewrite VD. simpl. repeat rewrite update_updated.
      reflexivity.
    + einstantiate trivial IHδ. destruct (vd v'); simpl;
      repeat rewrite update_frame; assumption.
Qed.

Theorem trim_delta_state_correct: forall vd δ h s0 s
  (HD: has_delta vd h s0 s δ), has_delta vd h s0 s (trim_delta_state vd δ).
Proof.
  unfold has_delta. intros. destruct (vd v) eqn: VD.
  - rewrite trim_delta_state_preserve in LUv by assumption.
    eapply HD; eassumption.
  - unfold trim_delta_state, init_delta in LUv. rewrite delta_updlst_def, VD in LUv.
    discriminate. intro InMap. unfold delta_defined in InMap.
    rewrite flat_map_concat_map, concat_map, map_map,
      <- flat_map_concat_map, in_flat_map in InMap.
    destruct InMap as [ [v' e'] [InDelta InVD] ].
    destruct (vd v') eqn: VD'; inversion InVD; subst; try inversion H.
    simpl in *. rewrite VD in VD'. discriminate.
Qed.

Lemma has_delta_assign_None: forall vd h s s' δ v u (HD: has_delta vd h s s' δ),
  has_delta vd h s (s' [v := u]) (δ [[v := None]]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite delta_update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    rewrite update_frame by assumption. eapply HD; eassumption.
Qed.

Lemma has_delta_assign_Some: forall vd h s s' δ v e u (HD: has_delta vd h s s' δ)
  (EQ: forall u' (EE: eval_exp h s e u'), u = u'),
  has_delta vd h s (s' [v := u]) (δ [[v := Some e]]).
Proof.
  unfold has_delta. intros. destruct (v == v0).
  - subst. rewrite update_updated. rewrite delta_update_updated in LUv.
    inversion LUv; subst. apply EQ. assumption.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    rewrite update_frame by assumption. eapply HD; eassumption.
Qed.

Lemma delta_nounk_assign_None: forall vd v δ (DNU: delta_nounk vd δ),
  delta_nounk vd (δ [[v := None]]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite delta_update_updated in LUv. discriminate.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Lemma delta_nounk_assign_Some: forall vd v δ e (DNU: delta_nounk vd δ)
  (NUnk: forall_exps_in_exp not_unknown e),
  delta_nounk vd (δ [[v := Some e]]).
Proof.
  unfold delta_nounk. intros. destruct (v == v0).
  - subst. rewrite delta_update_updated in LUv. inversion LUv; subst. assumption.
  - apply neq_sym in n. rewrite delta_update_frame in LUv by assumption.
    eapply DNU; eassumption.
Qed.

Theorem delta_same_domain_refl: forall vd δ, delta_same_domain vd δ δ.
Proof.
  unfold delta_same_domain. intros.
  destruct (δ<{vd}>[[v]]); reflexivity.
Qed.

Theorem delta_same_domain_assign: forall vd v δ1 δ2 o1 o2
  (Sim: match o1, o2 with
        | Some _, Some _ => True
        | None, None => True
        | _, _ => False
        end)
  (DSD: delta_same_domain vd δ1 δ2),
  delta_same_domain vd (δ1[[v := o1]]) (δ2[[v := o2]]).
Proof.
  unfold delta_same_domain. intros. destruct (v == v0).
  - subst. repeat rewrite delta_update_updated. destruct o1, o2;
    solve [reflexivity|contradiction Sim].
  - apply neq_sym in n. repeat rewrite delta_update_frame by assumption. apply DSD.
Qed.

Theorem subst_valid_any_Some: forall vd e δ1 δ2
  (DSD: delta_same_domain vd δ1 δ2),
  subst_valid vd δ1 e = subst_valid vd δ2 e.
Proof.
  induction e; intros; simpl; try erewrite IHe1 by eassumption;
  try erewrite IHe2 by eassumption; try erewrite IHe3 by eassumption;
  try erewrite IHe by eassumption; try reflexivity.

  (* Var *) specialize (DSD v). destruct (δ1<{vd}>[[v]]), (δ2<{vd}>[[v]]);
  try solve [contradiction DSD|reflexivity].

  (* Let *) destruct subst_valid eqn: SV1; erewrite IHe2; try reflexivity;
  (apply delta_same_domain_assign; [reflexivity|assumption]).
Qed.

Local Ltac exp_destruction_nounk :=
  lazymatch goal with
  | δ: store_delta |- _ =>
      (* Specialize the δ, allowing destruct to do automatic rewrites *)
      repeat match goal with
             | IH: forall (δ0: store_delta), _ |- _ => specialize (IH δ)
             end;
      (* Destruct on all the subst_valid _ e? *)
      repeat destruct (subst_valid _ _); inversion SE;
      (* Destruct on any conditionals *)
      repeat match goal with
             | n: N |- _ => destruct n
             end;
      repeat lazymatch goal with
             | IH: forall (DNU: delta_nounk _ δ), _ |- _ =>
                 einstantiate trivial IH as IH
             end
  end.

Theorem subst_exp0_nounk: forall vd e δ (DNU: delta_nounk vd δ)
  (SE: subst_valid vd δ e = true),
  forall_exps_in_exp not_unknown (subst_exp0 vd δ e).
Proof.
  unfold subst_exp; induction e; intros; simpl in SE;
  try solve [exp_destruction_nounk; repeat split; assumption + reflexivity].
  - (* Var *) destruct (δ<{vd}>[[v]]) eqn: LUv; inversion SE. subst. eapply DNU.
    simpl. rewrite LUv. reflexivity.
  - (* Let *) simpl. destruct subst_valid eqn: SV1.
    + (* e1 is valid *) apply IHe2. apply delta_nounk_assign_Some. assumption.
      apply IHe1; assumption. erewrite subst_valid_any_Some. eassumption.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) apply IHe2. apply delta_nounk_assign_None.
      assumption. assumption.
Qed.

Theorem subst_exp_nounk: forall vd e e' δ (DNU: delta_nounk vd δ)
  (SE: subst_exp vd δ e = Some e'), forall_exps_in_exp not_unknown e'.
Proof.
  unfold subst_exp. intros. destruct subst_valid eqn: SV; inversion SE.
  subst. apply subst_exp0_nounk; assumption.
Qed.

Local Ltac exp_destruction_correct :=
  lazymatch goal with
  | δ: store_delta, e': exp |- _ =>
      lazymatch goal with
      | SE: _ = Some e', EE': eval_exp _ _ e' _ |- _ =>
          (* Specialize the δ, allowing destruct to do automatic rewrites *)
          repeat match goal with
                 | IH: forall (δ0: store_delta), _ |- _ => specialize (IH δ)
                 end;
          (* Destruct on all the subst_valid _ e? *)
          repeat destruct (subst_valid _ _);
          (* Do rest of inversions *)
          inversion SE; subst; inversion EE'; subst;
          (* Destruct on any conditionals *)
          repeat match goal with
                 | n: N |- _ => destruct n
                 end;
          repeat lazymatch goal with
                 | IH: forall (e': exp), _ |- _ =>
                     einstantiate trivial IH as IH; inversion IH
                 end
      end
  end.

Lemma null_models: forall c, exists s, models c s.
Proof.
  intros. exists (fun v =>
    match c v with
    | Some (NumT w) => VaN 0 w
    | Some (MemT w) => VaM (fun _ => 0) w
    | None => VaN 0 1
    end).
  intros v t LU. rewrite LU.
  destruct t.
  - constructor. destruct w; reflexivity.
  - constructor. intro a. reflexivity.
Qed.

Lemma simplify_exp_eval_sound: forall h s e n w
  (SIMP: simplify_exp_eval e = Some (n, w)),
  eval_exp h s e (VaN n w).
Proof.
  induction e; intros; try discriminate; simpl in SIMP.
  - (* Word *) inversion SIMP. constructor.
  - (* binop *) destruct simplify_exp_eval as [ [n1' w1]|] eqn: SIMP1; try discriminate.
    destruct (simplify_exp_eval e2) as [ [n2' w2]|] eqn: SIMP2; try discriminate.
    destruct (w1 == w2); try discriminate. subst.
    destruct eval_binop as [n' w'|] eqn: EB; inversion SIMP. subst. rewrite <- EB.
    repeat constructor. einstantiate trivial IHe1 as IHe1.
    einstantiate trivial IHe2 as IHe2.
  - (* Unop *) destruct simplify_exp_eval as [ [n1' w1']|] eqn: SIMP1; try discriminate.
    destruct eval_unop as [n' w'|] eqn: EB; try discriminate. inversion SIMP.
    subst. rewrite <- EB. constructor. einstantiate trivial IHe as IHe.
  - (* Cast *) destruct simplify_exp_eval as [ [n1' w1']|] eqn: SIMP1; try discriminate.
    inversion SIMP. subst. constructor. einstantiate trivial IHe as IHe.
  - (* Ite *) destruct simplify_exp_eval as [ [n1' w1']|] eqn: SIMP1; try discriminate.
    einstantiate trivial EIte. einstantiate trivial IHe1.
    destruct n1'; [einstantiate trivial IHe3|einstantiate trivial IHe2].
  - (* Extract *) destruct simplify_exp_eval as [ [n' w']|] eqn: SIMP1; try discriminate.
    inversion SIMP. subst. econstructor. einstantiate trivial IHe as IHe.
  - (* Concat *) destruct simplify_exp_eval as [ [n1' w1']|] eqn: SIMP1; try discriminate.
    destruct (simplify_exp_eval e2) as [ [n2' w2']|] eqn: SIMP2; try discriminate.
    inversion SIMP. subst. constructor. einstantiate trivial IHe1.
    einstantiate trivial IHe2.
Qed.

Lemma eval_binop_num_correct: forall bop w n1 n2,
  VaN (eval_binop_num bop w n1 n2) (widthof_binop bop w) = eval_binop bop w n1 n2.
Proof. unfold eval_binop_num. intros. destruct bop; reflexivity. Qed.

Lemma eval_binop_num_bounded: forall bop w n1 n2 (LT1: n1 < 2 ^ w)
  (LT2: n2 < 2 ^ w), eval_binop_num bop w n1 n2 < 2 ^ (widthof_binop bop w).
Proof.
  intros. einversion typesafe_binop; try constructor. exact LT1. exact LT2.
  rewrite <- eval_binop_num_correct in H1. inversion H1. subst. eassumption.
Qed.

Lemma hastyp_SExp: forall c e t,
  hastyp_exp c e t <-> hastyp_se c (SExp e) t.
Proof. intros. split; intros TE; [constructor|inversion TE]; assumption. Qed.

Lemma preservation_se_exp: forall se c t,
  hastyp_se c se t <-> hastyp_exp c (se_to_exp se) t.
Proof.
  intros. destruct se; simpl.
  - split; intro TE; inversion TE; constructor; assumption.
  - rewrite hastyp_SExp. apply iff_refl.
  - split; [intro TSE|intro TE].
    + inversion TSE. subst. unsimpl (widthof_binop OP_PLUS w).
      repeat constructor; assumption.
    + inversion TE. inversion T2. subst. constructor; assumption.
Qed.

Lemma eval_binop_plus_0_r: forall w n, n < 2 ^ w ->
  VaN n w = eval_binop OP_PLUS w n 0.
Proof. intros. simpl. rewrite N.add_0_r, N.mod_small; trivial2. Qed.

Lemma se_eval_binop_type_sound: forall flipped op w n1 c e n2 t1 t2
  (TE: hastyp_exp c (se_to_exp (se_eval_binop flipped w op n1 e n2)) t2)
  (TSE: hastyp_se c (se_eval_binop flipped w op n1 e n2) t1), t1 = t2.
Proof.
  intros. destruct flipped.
  - destruct op; inversion TSE; inversion TE; subst;
    try solve [inversion TE0; inversion T2; inversion T3; subst; reflexivity].
    + (* Plus *) inversion T2. subst. reflexivity.
    + (* Minus *) inversion T2. subst. reflexivity.
  - destruct op; inversion TSE; inversion TE; subst;
    try solve [inversion TE0; inversion T0; inversion T1; subst; reflexivity].
    inversion T2. subst. reflexivity.
Qed.

Lemma preservation_se_eval_binop: forall flipped op w n1 c e n2 t
  (TSE1: hastyp_se c (SWord n1 w) t) (TSE2: hastyp_se c (SExpOff e n2 w) t),
  hastyp_se c (se_eval_binop flipped w op n1 e n2) (NumT (widthof_binop op w)).
Proof.
  intros. inversion TSE1. inversion TSE2. subst. destruct flipped.
  - destruct op; repeat constructor; try apply preservation_se_exp;
    try solve [destruct w; trivial2|trivial2];
    apply N.mod_lt; destruct w; discriminate.
  - destruct op; repeat constructor; try apply preservation_se_exp;
    try solve [destruct w; trivial2|trivial2];
    apply N.mod_lt; destruct w; discriminate.
Qed.

Lemma mod_2pow_lt: forall n w, n mod 2 ^ w < 2 ^ w.
Proof. intros. apply N.mod_lt. destruct w; discriminate. Qed.

Lemma mod_mod2: forall a n, (a mod n) mod n = a mod n.
Proof. intros. destruct n, a; try reflexivity. apply N.mod_mod. discriminate. Qed.

Lemma se_eval_binop_sound: forall (flipped: bool) h s w op n1 c e n2 v t
  (MDL: models c s) (TSE1: hastyp_se c (SWord n1 w) t)
  (TSE2: hastyp_se c (SExpOff e n2 w) t),
  (if flipped then
    eval_exp h s (BinOp op (se_to_exp (SExpOff e n2 w))
      (se_to_exp (SWord n1 w))) v
  else
    eval_exp h s (BinOp op (se_to_exp (SWord n1 w))
      (se_to_exp (SExpOff e n2 w))) v) <->
  eval_exp h s (se_to_exp (se_eval_binop flipped w op n1 e n2)) v.
Proof.
  intros. inversion TSE2. inversion TSE1. subst.
  einstantiate trivial (preservation_se_eval_binop flipped op) as TSE_binop.
  destruct flipped.
  - split; intro EE.
    + destruct op; try assumption; inversion EE; inversion E1; inversion E2;
      inversion E3; subst; clear EE E1 E2 H17;
      (assert (2 ^ w0 <> 0); [destruct w0; discriminate|]); simpl.
      * (* Plus *) rewrite N.add_mod_idemp_l, <- N.add_assoc,
          <- (N.add_mod_idemp_r n4) by assumption.
        unsimpl (eval_binop OP_PLUS _ _ _). repeat constructor. assumption.
      * (* Sub *) simpl. apply N.lt_le_incl in LT0.
        rewrite mod_sub_extract, mod_mod2, N.add_mod_idemp_l, <- N.add_assoc,
          <- N.add_mod_idemp_r, N.add_sub_assoc; trivial2.
        unsimpl (eval_binop OP_PLUS _ _ _). repeat constructor. assumption.
    + simpl. destruct op; inversion EE; subst; try (constructor; assumption).
      * (* Plus *) assert (2 ^ w0 <> 0). destruct w0; discriminate.
        inversion E2. subst. simpl. rewrite N.add_mod_idemp_r,
          N.add_assoc, <- N.add_mod_idemp_l by assumption.
        unsimpl (eval_binop OP_PLUS w0 _ _). repeat constructor.
        unsimpl (eval_binop OP_PLUS w0 _ _). repeat constructor. assumption.
      * (* Minus *) assert (2 ^ w0 <> 0). destruct w0; discriminate.
        inversion E2. subst. simpl. apply N.lt_le_incl in LT0.
        rewrite N.add_mod_idemp_r, <- N.add_sub_assoc, N.add_assoc,
          <- N.add_mod_idemp_l, <- (mod_mod2 (n0 + n2)),
          <- mod_sub_extract by trivial2.
        unsimpl (eval_binop OP_MINUS _ _ _). repeat constructor.
        unsimpl (eval_binop OP_PLUS _ _ _). repeat constructor. assumption.
  - split; intro EE.
    + destruct op; try assumption. inversion EE. inversion E1. inversion E2.
      inversion E3. subst. clear EE E1 E2 E3 H17. simpl.
      assert (2 ^ w0 <> 0). destruct w0; discriminate.
      rewrite N.add_mod_idemp_r, (N.add_comm n0), <- N.add_assoc,
        <- (N.add_mod_idemp_r n4) by assumption.
      unsimpl (eval_binop OP_PLUS _ _ _). repeat constructor. assumption.
    + destruct op; try assumption. inversion EE. subst.
      assert (2 ^ w0 <> 0). destruct w0; discriminate.
      inversion E2. subst. simpl. rewrite N.add_mod_idemp_r, N.add_assoc,
        (N.add_comm _ n1), <- N.add_mod_idemp_r by assumption.
      unsimpl (eval_binop OP_PLUS w0 _ _). repeat constructor.
      unsimpl (eval_binop OP_PLUS w0 _ _). repeat constructor. assumption.
Qed.

Lemma preservation_simplify_exp_eval: forall c e t n w
  (EVAL: simplify_exp_eval e = Some (n, w)) (TE: hastyp_exp c e t),
  hastyp_se c (SWord n w) t.
Proof.
  intros. einversion null_models as [s MDL].
  einstantiate trivial (simplify_exp_eval_sound htotal) as EE.
  einversion trivial @preservation_eval_exp. inversion H1. subst.
  constructor. assumption.
Qed.

Lemma preservation_simplify_exp_arith0: forall e c t
  (TE: hastyp_exp c e t), hastyp_se c (simplify_exp_arith0 c e) t.
Proof.
  induction e; intros; simpl; inversion TE; subst;
  match type of TE with
  | hastyp_exp ?c ?e _ =>
      try (try unsimpl (simplify_exp_eval e);
      destruct (simplify_exp_eval _) as [ [? ?]|] eqn: EVAL;
      [einstantiate trivial (preservation_simplify_exp_eval c e)|])
  end.
  - (* Var *) apply hastyp_SExp. assumption.
  - (* Word *) constructor. assumption.
  - (* Load *) rewrite <- hastyp_SExp. econstructor; apply preservation_se_exp.
    einstantiate trivial IHe1. einstantiate trivial IHe2.
  - (* Store *) rewrite <- hastyp_SExp. econstructor; apply preservation_se_exp.
    einstantiate trivial IHe1. einstantiate trivial IHe2. einstantiate trivial IHe3.
  - (* Binop *) assert (0 < 2 ^ w). destruct w; reflexivity.
    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    destruct simplify_exp_arith0 eqn: SE1, (simplify_exp_arith0 c e2) eqn: SE2;
    inversion IHe1; inversion IHe2; subst;
    repeat match goal with
           | H: NumT _ = NumT _ |- _ => inversion H; subst; clear H
           end;
    try solve
      [ eapply preservation_se_eval_binop; econstructor; trivial2
      | repeat econstructor; trivial2
      | repeat econstructor; apply preservation_se_exp;
          repeat econstructor; trivial2
      ].
  - (* Unop *) repeat econstructor. apply preservation_se_exp. einstantiate trivial IHe.
  - (* Cast *) einstantiate trivial IHe. destruct typchk_exp as [ [|]|] eqn: TCHK;
    try (repeat econstructor; try apply preservation_se_exp; trivial2).
    destruct (w == w1);
      try (repeat econstructor; try apply preservation_se_exp; trivial2).
    subst. einstantiate trivial typchk_exp_sound as SOUND. einstantiate trivial IHe.
  - (* Let *) destruct typchk_exp eqn: CHK; [|constructor; assumption].
    apply hastyp_SExp. einstantiate trivial typchk_exp_sound as SOUND.
    apply preservation_se_exp in SOUND. einstantiate trivial IHe1 as IHe1.
    einstantiate trivial IHe2 as IHe2. einstantiate hastyp_se_deterministic.
    exact IHe1. exact SOUND. subst. econstructor; apply preservation_se_exp;
    trivial2.
  - (* Unknown *) constructor. assumption.
  - (* Ite *) constructor. econstructor; apply preservation_se_exp.
    einstantiate trivial IHe1. einstantiate trivial IHe2. einstantiate trivial IHe3.
  - (* Extract *) constructor. econstructor. apply preservation_se_exp.
    einstantiate trivial IHe. assumption.
  - (* Concat *) constructor. econstructor; apply preservation_se_exp.
    einstantiate trivial IHe1. einstantiate trivial IHe2.
Qed.

Lemma simplify_exp_arith0_eval_type_sound: forall e c t1 t2 n w
  (EVAL: simplify_exp_eval e = Some (n, w))
  (TE: hastyp_exp c e t1) (TSE: hastyp_se c (SWord n w) t2),
  t1 = t2.
Proof.
  intros. einversion null_models as [s MDL].
  einstantiate trivial (simplify_exp_eval_sound htotal) as EE.
  einversion trivial @preservation_eval_exp. inversion H1. subst.
  inversion TSE. reflexivity.
Qed.

Lemma simplify_exp_arith0_type_sound: forall e c t1 t2
  (TE: hastyp_exp c e t1) (TSE: hastyp_se c (simplify_exp_arith0 c e) t2),
  t1 = t2.
Proof.
  intros. apply preservation_simplify_exp_arith0 in TE.
  einstantiate hastyp_se_deterministic. exact TE. exact TSE. assumption.
Qed.


Lemma simplify_exp_arith_sound_if_eval: forall h e s c v' v
  (EVAL: simplify_exp_eval e = Some v')
  (NU: forall_exps_in_exp not_unknown e),
  eval_exp h s e v <-> eval_exp h s (simplify_exp_arith c e) v.
Proof.
  intros. destruct v' as [n w]. einstantiate trivial simplify_exp_eval_sound as EE.
  split; intros EE2.
  - specialize (eval_exp_deterministic NU EE EE2) as EQ. subst.
    destruct e; unfold simplify_exp_arith, simplify_exp_arith0;
    rewrite EVAL; econstructor.
  - destruct e; unfold simplify_exp_arith, simplify_exp_arith0 in EE2;
    rewrite EVAL in EE2; inversion EE2; assumption.
Qed.

Lemma cast_same_bitwidth_preserves: forall c w n,
  n < 2 ^ w -> cast c w w n = n.
Proof.
  intros. destruct c; simpl.
  - (* LOW *) apply N.mod_small. assumption.
  - (* HIGH *) rewrite N.sub_diag. reflexivity.
  - (* SIGNED *) unfold scast. rewrite ofZ_toZ. apply N.mod_small. assumption.
  - (* UNSIGNED *) reflexivity.
Qed.

Local Ltac sexp_arith_sound_triv :=
  let EE := fresh "EE" in
  split; intros EE; inversion EE; subst; econstructor;
  match goal with
  | IH: forall c, _ |- _ => eapply IH; try eassumption
  end.

Lemma eval_binop_inj: forall {h s op e1 e1' e2 e2' v'}
  (E1: forall v1, eval_exp h s e1 v1 <-> eval_exp h s e1' v1)
  (E2: forall v2, eval_exp h s e2 v2 <-> eval_exp h s e2' v2),
  eval_exp h s (BinOp op e1 e2) v' <-> eval_exp h s (BinOp op e1' e2') v'.
Proof.
  split; intros EE; inversion EE; subst; econstructor;
  try apply E1; try apply E2; eassumption.
Qed.

Lemma eval_se_offset_0: forall h c s e v2 w
  (MDL: models c s) (TE: hastyp_exp c e (NumT w)),
  eval_exp h s (se_to_exp (SExp e)) v2 <-> eval_exp h s (se_to_exp (SExpOff e 0 w)) v2.
Proof.
  intros. simpl. split; intros EE.
  - einversion trivial @preservation_eval_exp. inversion H2. subst.
    erewrite <- (N.mod_small n), <- (N.add_0_r n) by eassumption.
    unsimpl (eval_binop OP_PLUS _ _ _). repeat econstructor. eassumption.
  - einversion EE. einversion E2. einversion trivial @preservation_eval_exp.
    inversion H2. inversion H1. subst. simpl. rewrite N.add_0_r, N.mod_small;
    assumption.
Qed.

Theorem simplify_exp_arith_sound: forall h e c s t v
  (MDL: models c s) (TE: hastyp_exp c e t) (NU: forall_exps_in_exp not_unknown e),
  eval_exp h s e v <-> eval_exp h s (simplify_exp_arith c e) v.
Proof.
  unfold simplify_exp_arith.
  induction e; intros; simpl; inversion TE; simpl in NU; decompose record NU; subst;
  (* First account for cases if we can simplify by fully evaluating the
   * expression *)
  match type of TE with
  | hastyp_exp ?c ?e _ =>
      try unsimpl (simplify_exp_eval e);
      try (destruct (simplify_exp_eval _) as [ [? ?]|] eqn: EVAL;
      [ try discriminate;
        einstantiate trivial simplify_exp_arith_sound_if_eval as EVAL_sound;
        unfold simplify_exp_arith in *; simpl in *; rewrite EVAL in *; trivial2 |])
  end;
  (* Solve trivial cases that directly follow from IH *)
  try solve [sexp_arith_sound_triv].
  - (* BinOp *) apply preservation_simplify_exp_arith0 in T1 as TSE1.
    apply preservation_simplify_exp_arith0 in T2 as TSE2.
    destruct simplify_exp_arith0 eqn: SE1,
    (simplify_exp_arith0 c e2) eqn: SE2;
    try solve
      [ rewrite <- SE1, <- SE2 in *; simpl; sexp_arith_sound_triv ];
    (* Solve cases that uses eval_binop *)
    inversion TSE1; inversion TSE2; subst;
    einstantiate trivial se_eval_binop_sound as SOUND;
    match goal with
    | _: hastyp_se _ (SExp _) _ |- hastyp_se c (SExpOff _ _ _) _ =>
        econstructor; [eassumption|apply Nlt_0_pow2]
    | |- eval_exp _ _ _ _ <-> eval_exp _ _ _ _ =>
        eapply iff_trans; [|eapply SOUND]
    end; eapply eval_binop_inj; intros;
    lazymatch goal with
    | SE: simplify_exp_arith0 _ ?e = SWord _ _ |-
      eval_exp _ _ _ _ <-> eval_exp _ _ (se_to_exp (SWord _ _)) _ =>
        rewrite <- SE
    | SE: simplify_exp_arith0 _ ?e = SExp _ |-
        eval_exp _ _ _ _ <-> eval_exp _ _ (se_to_exp (SExpOff _ _ _)) _ =>
        rewrite <- eval_se_offset_0, <- SE by eassumption
    | SE: simplify_exp_arith0 _ ?e = SExpOff _ _ _ |-
        eval_exp _ _ _ _ <-> eval_exp _ _ (se_to_exp (SExpOff _ _ _)) _ =>
        rewrite <- SE
    end; einstantiate trivial IHe1; einstantiate trivial IHe2.
    Unshelve.
    all: match goal with
         | c: typctx |- typctx => exact c
         | v: value |- value => exact v
         | _ => idtac
         end.
  - (* Cast *) destruct typchk_exp eqn: CHK; [|sexp_arith_sound_triv].
    destruct t; [|sexp_arith_sound_triv].
    destruct (w == w1); [|sexp_arith_sound_triv]. subst.
    apply typchk_exp_sound in CHK. einstantiate hastyp_exp_unique as EQ.
    apply hub_refl. exact CHK. exact T1. inversion EQ. subst.
    split; intros EE.
    + inversion EE; subst. clear EE. einversion trivial @preservation_eval_exp.
      inversion H1. inversion H2. subst. einstantiate trivial IHe as IHe.
      apply IHe. rewrite cast_same_bitwidth_preserves; assumption.
    + einstantiate trivial IHe as IHe. apply IHe in EE.
      einversion trivial @preservation_eval_exp. inversion H2. subst.
      einstantiate trivial ECast as EE2.
      erewrite cast_same_bitwidth_preserves in EE2; eassumption.
  - (* Let *) destruct typchk_exp eqn: CHK; [|apply iff_refl].
    apply typchk_exp_sound in CHK. apply preservation_se_exp in CHK.
    einstantiate trivial (simplify_exp_arith0_type_sound e1). subst.
    simpl. sexp_arith_sound_triv. eapply models_assign; trivial2.
    eapply models_assign; trivial2. einstantiate trivial IHe1 as IHe1.
    apply IHe1. eassumption.
  - (* Unknown *) inversion NU.
  - (* Ite *) split; intros EE; inversion EE; subst; econstructor;
    try eapply IHe1; try eassumption; destruct n1; try eapply IHe2;
    try eapply IHe3; try eassumption.
Qed.

Theorem subst_exp_correct: forall vd s0 h e e' s δ v v'
  (HD: has_delta vd h s0 s δ) (SE: subst_exp vd δ e = Some e') (EE: eval_exp h s e v)
  (EE': eval_exp h s0 e' v'), v = v'.
Proof.

  intros. move δ before e. repeat lazymatch goal with H:_ |- _ => revert H end.

  unfold subst_exp; induction e; intros; inversion EE; subst;
  simpl in SE; clear EE; try solve [exp_destruction_correct; reflexivity].
  - (* Var *) destruct (δ<{vd}>[[v]]) eqn: LUv; inversion SE. subst. erewrite HD;
    solve [reflexivity|eassumption].
  - (* Let *) destruct subst_valid eqn: SV1.
    + (* e1 is valid *) erewrite subst_valid_any_Some in SE. eapply IHe2;
      [| eassumption | eassumption | eassumption]. apply has_delta_assign_Some.
      assumption. intros. destruct (subst_valid _ _ e2) eqn: SV2; inversion SE.
      eapply IHe1; try eassumption. rewrite SV1. reflexivity.
      apply delta_same_domain_assign. reflexivity. apply delta_same_domain_refl.
    + (* e1 is not valid *) eapply IHe2; [| eassumption | eassumption | eassumption].
      apply has_delta_assign_None. assumption.
  - (* Ite *) exp_destruction_correct. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe1 as IHe1.
      einstantiate trivial IHe2 as IHe2.
Qed.

Theorem map_option_inductive_principal: forall {A B} (P: list A -> list B -> Prop)
  al bl (f: A -> option B) (MAPS: map_option f al = Some bl) (BASE: P nil nil)
  (INDUCT: forall a b (F: f a = Some b) al bl (MO: map_option f al = Some bl)
    (IHab: P al bl), P (a :: al) (b :: bl)),
  P al bl.
Proof.
  induction al; intros.
  - inversion MAPS. exact BASE.
  - inversion MAPS. destruct (f a) eqn: F; inversion H0. clear H0.
    destruct (map_option _ al) eqn: MO; try inversion H1. subst. clear H1.
    apply INDUCT; try assumption. eapply IHal; try solve [eassumption|reflexivity].
Qed.

Tactic Notation "induction_map" ident(al) "maps_to" ident(bl) :=
  (first [ revert dependent al; intro al; revert dependent bl; intros bl
         | intros until al; intros until bl] ||
  fail "No quantified hypothesis for" al "or" bl);
  repeat lazymatch goal with
         | [H: ?HType |- _] =>
             lazymatch HType with
             | map_option ?f al = Some bl => fail
             | _ => intro
             end
         end;
  let typ := uconstr:(map_option ?f al = Some bl) in
  pattern al, bl; eapply map_option_inductive_principal;
  [intros; (eassumption||fail "No quantified hypothesis to satisfy " typ)
  | | intro; intro; intro; intro; intro; intro; intro ].

Lemma map_option_includes: forall A B (f: A -> option B) l l'
  (Maps: map_option f l = Some l') a b (F: f a = Some b) (InL: In a l),
  In b l'.
Proof.
  induction l.
    intros. simpl in Maps. inversion InL.
    intros. simpl in Maps. destruct f eqn:DF; try solve [inversion Maps].
      destruct (map_option); inversion Maps.
      inversion InL.
        subst. rewrite DF in F. inversion F. subst. constructor. reflexivity.
        destruct l'; try solve [inversion H0]. apply in_cons. clear DF Maps InL H0 a. eapply IHl.
          reflexivity. apply F. assumption.
Qed.

Lemma map_option_fails: forall A B (f: A -> option B) l a
  (F: f a = None) (InL: In a l), map_option f l = None.
Proof.
  induction l; intros.
  - inversion InL.
  - inversion InL; subst.
    + simpl. rewrite F. reflexivity.
    + simpl. erewrite IHl; try eassumption. destruct (f a); reflexivity.
Qed.

Theorem simple_trace_stmt0_correct: forall hints vd q q0 paths h p n
  a0 s0 s0' a1 s1 x2 s2 δ evs c
  (HD: has_delta vd h s0 s1 δ) (XS: exec_stmt h s1 q s2 x2)
  (LU2: forall a2, x2 = Some (Exit a2) -> exists insn, p s2 a2 = Some insn)
  (STS: simple_trace_stmt0 hints vd δ a1 q0 q c = Some (paths, evs))
  (XP: exec_prog h p a0 s0 n s0' (Exit a1))
  (XS0: exec_stmt h s0' q0 s1 None)
  (EV: sat_evidences evs p h a0 s0),
  Exists (fun '(δ', x') => x' = x2 /\ has_delta vd h s0 s2 δ') paths.
Proof.
  induction q; intros; inversion XS; inversion STS; subst; clear STS.
  - (* Nop *) constructor. split; trivial2.
  - (* Move *) constructor. split. reflexivity. destruct subst_exp eqn: SE1;
    [|apply has_delta_assign_None; assumption]. apply has_delta_assign_Some.
    assumption. intros. apply <- simplify_exp_arith_sound in EE.
    eapply subst_exp_correct; eassumption. admit. admit. admit.
  - (* Jmp *) destruct hints as [jmps|].
    + (* Use hint *) inversion H3. subst. clear H3. inversion EV. inversion H1.
      subst. einstantiate trivial EJT as EJT. apply Exists_exists in EJT.
      apply Exists_exists. einversion trivial LU2 as [insn LU'].
      destruct EJT as [j [InJmps EJ] ]. inversion EJ;
      [|rewrite LU in LU'; discriminate]. subst. clear EJ.
      eexists. split. apply in_flat_map. eexists. split; [eassumption|].
      simpl. left. reflexivity. simpl. split; trivial2.
    + (* No hint *) destruct (subst_exp _ _ _) eqn: SE; try destruct e0; inversion H3.
      subst. constructor. split; [|assumption].
      einstantiate trivial subst_exp_correct as Res. constructor. inversion Res.
      subst. reflexivity.
  - (* Exn *) constructor. split; trivial2.
  - (* Seq, exit 1 *) destruct simple_trace_stmt0 as [res1|] eqn: SQ1; try discriminate.
    destruct res1 as [paths1 ev1]. destruct map_option as [path_res|] eqn: Map;
    inversion H4. subst. clear XS H4. apply Forall_app in EV.
    destruct EV as [EV EV1]. einstantiate trivial IHq1. apply Exists_exists in H.
    destruct H as [ [δ1 x1] [InP1 [X HD1] ] ]; subst. apply Exists_exists.
    exists (δ1, Some x). repeat split; try assumption. apply in_concat. eexists.
    split; [|apply in_eq].  eapply map_option_includes; try eassumption. reflexivity.
  - (* Seq, exit 2 *) destruct simple_trace_stmt0 as [res1|] eqn:SQ1; [|discriminate].
    destruct res1 as [paths1 ev1]. destruct map_option as [path_res|] eqn: Map;
    inversion H4. subst. clear XS H4. apply Forall_app in EV. destruct EV as [EV EV1].
    einstantiate trivial IHq1. apply Exists_exists in H.
    destruct H as [ [δ1 x1] [InP1 [X HD1] ] ]; subst. apply Exists_exists.
    destruct (simple_trace_stmt0 hints vd δ1 a1 (Seq q0 q1) q2 c)
        as [ [paths2 ev2]|] eqn:SQ2.
    + (* Expand out IHq2. We have to show that ev2 is part of ev' *)
      einstantiate trivial IHq2 as IHq2. econstructor; eassumption.
      unfold sat_evidences. rewrite Forall_forall in *. intros ev' InEV2.
      einstantiate trivial EV. apply in_flat_map. eexists. split. eassumption.
      simpl. rewrite SQ2. eassumption. rewrite Exists_exists in IHq2.
      destruct IHq2 as [ [δ' x'] [InP2 [EQ HD'] ] ]. subst.

      (* From IHq2, show that delta holds since the state is in (concat path_res) *)
      eexists. split. apply in_concat. eexists. split; [|eassumption].
      eapply map_option_includes; try eassumption. simpl. rewrite SQ2.
      reflexivity. simpl. split; trivial2.
    + erewrite map_option_fails in Map; try solve [discriminate|eassumption].
      simpl. rewrite SQ2. reflexivity.
  - (* If/else *) destruct c0;
    (destruct (simple_trace_stmt0) as [ [paths1 ev1]|] eqn: ST1; [|discriminate]);
    (destruct (simple_trace_stmt0 _ _ _ _ _ q2) as [ [paths2 ev2]|] eqn: ST2;
        [|discriminate]); inversion H5; subst; apply Forall_app in EV;
    destruct EV.
    + (* q2 *) einstantiate trivial IHq2. eapply incl_Exists.
      apply incl_appr. apply incl_refl. assumption.
    + (* q1 *) einstantiate trivial IHq1. eapply incl_Exists.
      apply incl_appl. apply incl_refl. assumption.
Admitted.

Theorem simple_trace_stmt_correct: forall hints vd q paths h p n
  a0 s0 a1 s1 x2 s2 c δ evs (XP: exec_prog h p a0 s0 n s1 (Exit a1))
  (HD: has_delta vd h s0 s1 δ) (XS: exec_stmt h s1 q s2 x2)
  (LU2: match x2 with
        | Some (Exit a2) => exists insn, p s2 a2 = Some insn
        | _ => True
        end)
  (STS: simple_trace_stmt hints vd δ a1 q c = Some (paths, evs))
  (EV: sat_evidences evs p h a0 s0),
  Exists (fun '(δ', x') => x' = x2 /\ has_delta vd h s0 s2 δ') paths.
Proof.
  intros. unfold simple_trace_stmt in STS.
  destruct simple_trace_stmt0 as [ [next_states evs']|] eqn: STS0; try discriminate.
  inversion STS. subst. clear STS. einstantiate trivial simple_trace_stmt0_correct.
  intros. subst. assumption. constructor. rewrite Exists_exists in *.
  destruct H as [ [δ' x'] [InX [EQ HD0] ] ]. subst.
  eexists (_, x2). repeat split. eassert (X: (_, x2) = _ _);
    [|rewrite X; apply in_map; eassumption]. reflexivity.
  apply trim_delta_state_correct. assumption.
Qed.

(*MARK*)

Theorem destruct_trace_program_step_at_prin: forall {P vd c p hints addr accum res}
  (TPSA: trace_program_step_at vd c p hints addr accum = Some res)
  (PInvalidLU: forall (TPSA': accum = Some res)
    (LU: p null_state addr = None), P addr)
  (PInvalidTS: forall ts changed evs sz q
    (TPSA': accum = Some res) (RES: res = (ts, changed, evs))
    (LU: p null_state addr = Some (sz, q))
    (TS: ts Ⓝ[ addr ] = None), P addr)
  (PDefault: forall ts changed evs evs' sz q δ_a next_states
    (TPSA': accum = Some (ts, changed, evs))
    (RES: res = (fold_right (process_state vd (exitof (addr + sz)))
      (ts, changed) next_states, evs' !++ evs))
    (LU: p null_state addr = Some (sz, q))
    (TS: ts Ⓝ[ addr ] = Some δ_a)
    (STS: simple_trace_stmt hints vd δ_a addr q c = Some (next_states, evs')),
    P addr), P addr.
Proof.
  intros. unfold trace_program_step_at in TPSA.
  destruct accum as [ [ [ts changed] old_evs]|]; try discriminate.
  destruct p as [ [sz q]|] eqn: LU; [|apply PInvalidLU; trivial2].
  destruct tget_n as [δ_a|] eqn: TS; [|inversion TPSA; subst;
      eapply PInvalidTS; trivial2].
  destruct simple_trace_stmt as [ [next_states evs]|] eqn: STS; inversion TPSA.
  subst. clear TPSA. eapply PDefault; trivial2.
Qed.

Ltac destruct_trace_program_step_at TPSA :=
  lazymatch type of TPSA with
  | trace_program_step_at _ _ _ _ ?addr _ = Some _ =>
      move TPSA before addr; revert dependent addr;
      intros addr TPSA; pattern addr;
      apply (destruct_trace_program_step_at_prin TPSA);
      intros; clear TPSA; subst
  | _ => fail "Expected hypothesis to be of the form trace_program_step_at ..."
  end.

Lemma process_state_nofold_nochange: forall vars xit k t b ts,
    process_state vars xit k (t, b) = (ts, false) -> (t, b) = (ts, false).
Proof.
  intros. unfold process_state in H.
  destruct k.
  destruct xit.
    destruct join_states_if_changed.
  inversion H. assumption. assumption.
Qed.

Lemma process_state_vars_nochange: forall l t b ts a n vars,
  fold_right (process_state vars (exitof (a + n))) (t, b) l = (ts, false) ->
    (t,b) = (ts,false).
Proof.
  induction l.
    intros. simpl in H. inversion H. reflexivity.
    intros. simpl in H. destruct fold_right eqn:H_fr in H.
    unfold process_state in H. destruct a. destruct (exitof (a0 + n) o) in H.
      destruct join_states_if_changed eqn:H_jsic in H; inversion H.
        subst. apply IHl in H_fr. inversion H_fr. reflexivity.
      inversion H. subst. apply IHl in H_fr. inversion H_fr. reflexivity.
Qed.

Lemma trace_program_step_at_nochange: forall vars p hints a2 inp ts ev c
   (TPSA: trace_program_step_at vars c p hints a2 inp = Some (ts, false, ev)),
   exists ev0, inp = Some (ts, false, ev0) /\ incl ev0 ev.
Proof.
  intros. destruct_trace_program_step_at TPSA.
  - eexists. split. reflexivity. apply incl_refl.
  - eexists. split. reflexivity. apply incl_refl.
  - eexists. inversion RES. split. f_equal. f_equal. subst.
    eapply process_state_vars_nochange. symmetry. eassumption.
    apply incl_appr, incl_refl.
Qed.

Theorem fold_trace_program_step_at_nochange:
  forall reachable_addrs vars p hints inp ts ev c
  (FR: fold_right (trace_program_step_at vars c p hints) inp
    reachable_addrs = Some (ts, false, ev)),
  exists ev0, inp = Some (ts, false, ev0) /\ incl ev0 ev.
Proof.
  induction reachable_addrs; intros; simpl in FR.
  - eexists. split. eassumption. apply incl_refl.
  - destruct fold_right eqn: FR0; try discriminate.
    edestruct trace_program_step_at_nochange as [ev0 [EQ EvIncl] ]; try eassumption.
    inversion EQ. subst. edestruct IHreachable_addrs as [ev1 [EQ2 Ev1Incl] ].
    eassumption. subst. eexists. split. reflexivity.
    eapply incl_tran; eassumption.
Qed.

Theorem trace_program_step_at_none_acc: forall l vars p c hints,
  fold_right (trace_program_step_at vars c p hints) None l = None.
Proof.
  induction l.
    intros. reflexivity.
    intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma delta_join_cases: forall vd δ1 δ2 v e
  (LU: (delta_join vd δ1 δ2)<{vd}>[[v]] = Some e),
  δ1<{vd}>[[v]] = Some e /\ δ2<{vd}>[[v]] = Some e.
Proof.
  unfold delta_join. intros. remember (delta_defined _) as domain eqn: DD.
  unshelve (edestruct (@in_dec var iseq); [|shelve]). shelve. shelve.
  - rewrite not_in_app in n. destruct n as [NIn1 NIn2].
    eapply delta_updlst_def in NIn1. rewrite NIn1.
    eapply delta_updlst_def in NIn2. rewrite NIn2. clear DD.
    revert LU. induction domain as [|v' domain IHdomain]; intros.
    + simpl in LU. split; assumption.
    + simpl in LU. unsimpl (delta_updlst _ (setlst _ v' _) v).
      destruct (v == v').
      * subst. rewrite NIn1, NIn2 in LU. vreflexivity (init_delta vd v').
        rewrite delta_update_updated in LU. split; assumption.
      * rewrite delta_update_frame in LU by assumption.
        apply IHdomain. assumption.
  - apply in_app_or in i as cases. rewrite <- delta_defined_app, <- DD in i.
    clear DD. induction domain as [|v' domain IHdomain]; intros.
    + inversion i.
    + simpl in LU. unsimpl (delta_updlst _ (setlst _ v' _) v).
      destruct (v == v').
      * subst. rewrite delta_update_updated in LU. destruct (_ == _);
        try discriminate. rewrite e0, LU. split; reflexivity.
      * rewrite delta_update_frame in LU by assumption.
        apply IHdomain. assumption. inversion i; try assumption.
        symmetry in H. contradiction n.
Qed.

Theorem expand_trace_program_steady_correct:
  forall vd c p hints ts h a0 s0 evs
  (INIT: exists δ, tget_n ts a0 = Some δ /\ has_delta vd h s0 s0 δ)
  (NWC: forall sa sb a, p sa a = p sb a)
  (TPO: expand_trace_program vd c p hints ts = Some (ts, false, evs))
  (SAT: sat_evidences evs p h a0 s0),
  correct_trace_prog vd p ts h a0 s0.
Proof.
  unfold correct_trace_prog, sat_evidences, expand_trace_program. intros.
  apply exec_prog_equiv_exec_prog2 in XP. revert a1 s1 sz' q' XP LU'.
  induction n1; intros; inversion XP; subst; try assumption.

  einversion trivial IHn1 as [δ_a2 [TS_a2 HD_a2] ].
  assert (InA2: In a2 (tkeys_n ts)). apply tkeys_n_in_contains.
    unfold tcontains_n. rewrite TS_a2. reflexivity.

  apply in_split in InA2. destruct InA2 as [r1 [r2 SPL] ]. rewrite SPL in *.
  rewrite fold_right_app in TPO. simpl in TPO.

  (* Destruct TPSA out *)
  destruct trace_program_step_at as [ [ [ts1 changed1] ev1]|] eqn: TPSA;
    [|rewrite trace_program_step_at_none_acc in TPO; discriminate].
  einversion fold_trace_program_step_at_nochange as [ev' [EQ EvIncl2] ]. exact TPO.
  inversion EQ. subst. clear EQ.

  (* Destruct inner fold_right *)
  destruct (fold_right _ _ r2) as [ [ [ts0 changed0] ev]|] eqn: FR0;
      try discriminate.
  einversion trace_program_step_at_nochange as [ev0 [EQ EvIncl] ]. exact TPSA.
  inversion EQ. subst. clear EQ FR0 TPO.

  (* Destruct TPSA *)
  destruct_trace_program_step_at TPSA.

  (* ERR: Invalid program address *)
  erewrite NWC, LU0 in LU. discriminate.

  (* ERR: Address not defined in ts *)
  inversion TPSA'. inversion RES. subst.
  rewrite TS_a2 in TS. discriminate.

  (* Show that when TPSA returns normally that it will give a correct value
     when we execute from a0 ~> a2 -> a1. *)
  inversion TPSA'. inversion RES. subst.
  erewrite NWC, LU in LU0. inversion LU0. subst. clear LU0 RES TPSA'.

  apply exec_prog_equiv_exec_prog2 in XP0 as XP0'.
  rewrite TS in TS_a2. inversion TS_a2. subst.
  einstantiate trivial simple_trace_stmt_correct as Correct.
    (* Prove p s1 a1 is defined with jumps *)
    destruct x' as [ [a1'|n]|]; try exact I. inversion H. subst.
    eexists. eassumption.

    (* Prove sat_evidences *)
    eapply incl_Forall in SAT; try exact EvIncl2. apply Forall_app in SAT.
    destruct SAT as [SAT _]. assumption.

  (* Corretness means next_states will contain a store_delta entry at a1
   * that has the proper delta. *)
  apply Exists_exists in Correct.
  destruct Correct as [ [δ_a1 x] [InSt [EQ HD] ] ]. subst.

  (* Take out the instance where process_state is processing our state *)
  apply in_split in InSt. destruct InSt as [ns1 [ns2 EQ] ]. subst.

  destruct fold_right eqn: FR_PS. inversion H4. symmetry in H1. subst.
  clear TS_a2 H4. rewrite fold_right_app in FR_PS. simpl in FR_PS.

  destruct process_state eqn: PS. apply process_state_vars_nochange in FR_PS.
  inversion FR_PS. subst. clear FR_PS.

  destruct fold_right. apply process_state_nofold_nochange in PS as PS'.
  inversion PS'. subst. clear PS'.

  (* Show that the delta written in trace states by process_state
     is a preserving delta. *)
  unfold process_state in PS. rewrite H in PS.
  destruct join_states_if_changed eqn: JS; try discriminate.
  unfold join_states_if_changed in JS.
  destruct (tget_n ts0 a1) as [δ_a1_old|] eqn: TS_a1; try discriminate.
  eexists. split. reflexivity. destruct delta_equivb eqn: EQB.
  - rewrite delta_equivb_iff_delta_equiv, delta_equiv_symm in EQB.
    eapply delta_equiv_has_delta; eassumption.
  - clear EQB. destruct delta_equivb eqn: EQB; try discriminate.
    rewrite delta_equivb_iff_delta_equiv, delta_equiv_symm in EQB.
    eapply delta_equiv_has_delta; try eassumption.
    intros v e val DJ EE. apply delta_join_cases in DJ.
    destruct DJ as [EQ1 EQ2]. eapply HD; eassumption.
Qed.

Theorem checked_trace_program_steady_correct:
  forall vd c p hints ts h a0 s0 evs
  (NWC: forall sa sb a, p sa a = p sb a)
  (CHK: check_trace_states vd c hints p ts a0 = Some evs )
  (SAT: sat_evidences evs p h a0 s0),
  correct_trace_prog vd p ts h a0 s0.
Proof.
  unfold check_trace_states. intros.
  destruct p as [x|] eqn: LU0; try discriminate.
  destruct tget_n as [δ|] eqn: TS; try discriminate.
  destruct forallb eqn: INIT; try discriminate.
  destruct expand_trace_program as [ [ [ts' [|] ] ev]|] eqn: ETP; try discriminate.
  inversion CHK. subst. clear CHK.

  unfold correct_trace_prog. intros.

  (* Prove etp returns properly *)
  assert (ts = ts'). unfold expand_trace_program in *.
  einversion trivial fold_trace_program_step_at_nochange as [ev [EQ Incl] ].
  inversion EQ. subst. reflexivity. subst.

  eapply expand_trace_program_steady_correct; try eassumption.

  (* Prove initial correctness *)
  eexists. split. eassumption. rewrite forallb_forall in INIT.
  intros v e val LU EE. edestruct delta_updlst_cases.
  - (* In delta store list *) einstantiate trivial INIT as EX.
    rewrite LU in EX. unfold iseqb in EX. destruct (e == Var v); try discriminate.
    subst. inversion EE. subst. reflexivity.
  - (* Using default value *) rewrite H in LU. clear H. unfold init_delta in LU.
    destruct vd; inversion LU. subst. inversion EE. subst. reflexivity.
Qed.

End PicinaeCalling.

Require Import Picinae_i386.
Require Import strchr_i386.
Import X86Notations.

Module Calling_i386 := PicinaeCalling IL_i386 Statics_i386.
Import Calling_i386.

Definition fh := htotal.

Definition simp_prog: program := fun _ a =>
  match a with

  (* 0x1: movl %esp, %ebp *)
  | 0 => Some (1,
      Move R_EBP (Var R_ESP)
  )
  | 1 => Some (1, Jmp (Word a 32))
  | _ => None
  end.

Theorem simp_prog_welltyped: welltyped_prog x86typctx simp_prog.
Proof.
  Picinae_typecheck.
Qed.

Definition simp_prog_jump_hints: jump_hint := fun a δ e => None.

Definition simp_prog_trace := expand_trace_program_n 10 (fun _ => true)
  x86typctx simp_prog_jump_hints simp_prog (tupdate_n treeN_nil 0 nil).

Goal True.
Proof.

  pose (x := match simp_prog_trace with
             | Some (ts, b, ev) =>
                 match tget_n ts 1 with
                 | Some δ => Some (ts, δ, b, ev)
                 | None => None
                 end
             | None => None
             end).
  compute in x.
Abort.

Require Import test.
Theorem my_prog_welltyped: welltyped_prog x86typctx my_prog.
Proof.
  Picinae_typecheck.
Qed.

Definition my_prog_jump_hints: jump_hint := fun a δ e =>
  match a with
  | 34 => Some (jump_symbolic :: nil)
  | _ => None
  end.

Definition domain1 var :=
  match var with
  | V_TEMP _ => false
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => false
  | _ => true
  end.

Definition my_prog_ts := Eval compute in
  compute_trace_program_n 100 domain1 x86typctx my_prog_jump_hints my_prog
    (init_ts 0).

Definition my_prog_trace :=
  expand_trace_program domain1 x86typctx my_prog my_prog_jump_hints my_prog_ts.

Goal forall esp0 s0 (MDL0: models x86typctx s0)
  (SV2: s0 R_ESP = Ⓓ esp0),
  exists val,
  eval_exp fh (s0 [ R_ESP := Ⓓ  42 ] [A_READ := Ⓜ (fun _ => 1)]
    [A_WRITE := Ⓜ (fun _ => 1)])
  (Load
     (Store
        (Store (Var V_MEM32) (BinOp OP_MINUS (Var R_ESP) (Word 4 32))
           (Cast CAST_LOW 32 (Var R_EBP)) LittleE 4)
        (BinOp OP_PLUS (BinOp OP_MINUS (Var R_ESP) (Word 4 32))
           (Word 4294967292 32)) (Word 0 32) LittleE 4)
     (BinOp OP_PLUS (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) (Word 4 32))
     LittleE 4) val.
Proof.
  intros.
  assert (MDL': models x86typctx (s0 [ R_ESP := Ⓓ  42 ] [A_READ := Ⓜ (fun _ => 1)]
    [A_WRITE := Ⓜ (fun _ => 1)])).
    intros v t eq. destruct v; psimpl;
    try solve [ eapply MDL0; eassumption
              | einversion eq; constructor; try intro; reflexivity].

  match goal with |- exists u, eval_exp ?h ?s ?e u =>
      mk_eval_exp h s e EE
  end.

  repeat split; try reflexivity; unfold mem_readable, mem_writable; psimpl;
  eexists; (split; [reflexivity|intro Contra; discriminate]).

  eexists. exact EE.
Qed.


Theorem getmem_frame_absdist: forall e1 e2 len1 len2 m a1 a2 v,
  len1 <= absdist a1 a2 -> len2 <= absdist a1 a2 ->
  getmem e1 len1 (setmem e2 len2 m a2 v) a1 = getmem e1 len1 m a1.
Proof.
  unfold absdist. intros. destruct (_ <=? _) eqn: LE.
  - apply N.leb_le in LE. specialize (le_add_le_sub_r_inv _ _ _ H LE). intro.
    apply getmem_frame_low. rewrite N.add_comm. assumption.
  - apply not_true_iff_false in LE. assert (a2 < a1).
    apply N.lt_nge. revert LE. contrapositive N.leb_le.
    apply getmem_frame_high. rewrite N.add_comm. apply le_add_le_sub_r_inv.
    assumption. intros X. rewrite H1 in X. discriminate.
Qed.

Theorem my_prog_nwc: forall s1 s2 a, my_prog s1 a = my_prog s2 a.
Proof. reflexivity. Qed.

Lemma mod_2pow_lt: forall n w, n mod 2 ^ w < 2 ^ w.
Proof. intros. apply N.mod_lt. destruct w; discriminate. Qed.

Theorem my_prog_hints_correct: forall esp0 mem s0 ts evs
  (ESP0: s0 R_ESP = Ⓓ esp0) (MEM0: s0 V_MEM32 = Ⓜmem)
  (RET: my_prog s0 (mem Ⓓ[ esp0 ]) = None)
  (WM: s0 A_WRITE = Ⓜ (fun _ => 1))
  (RM: s0 A_READ = Ⓜ (fun _ => 1))
  (MDL0: models x86typctx s0) (MPT: my_prog_trace = Some (ts, false, evs)),
  sat_evidences evs my_prog fh 0 s0.
Proof.
  intros. vm_compute in MPT. inversion MPT. subst. clear MPT.
  repeat constructor. eassert (MDL': models _ s1).
    eapply preservation_exec_stmt; [| |exact XS0].
    eapply preservation_exec_prog; [|exact my_prog_welltyped|]; eassumption.
    eapply typchk_stmt_sound; reflexivity. simpl in MDL'.

  step_stmt XS. destruct XS as [ [? ?] ? ]. inversion H0. subst.

  concretize_delta HD (V_TEMP 6).

  (* Prove memory accesses *)
  repeat split; try reflexivity; unfold mem_readable, mem_writable; psimpl;
  eexists; (split; [apply WM + apply RM|intro Contra; discriminate]).

  psimpl in Hsv1. rewrite Hsv1 in Hsv. remember (2 ^ 32). inversion Hsv.
  subst. repeat unsimpl (getmem LittleE 4 _ _). repeat unsimpl (setmem LittleE 4 _ _).
  specialize (x86_regsize MDL0 ESP0) as ESP_BND. cbv beta match delta [x86typctx] in ESP_BND.

  repeat rewrite getmem_frame_absdist; trivial2;
  erewrite N.add_comm, <- modabsdist_eq_absdist, modr_modabsdist; trivial2;
  try apply mod_2pow_lt;
  einversion trivial (modabsdist_add_l (2 ^ 32)) as [MAD|MAD];
        rewrite MAD; discriminate.
Qed.

Definition trace_invs (post: exit -> store -> Prop) :=
  invs (fun _ _ => Some True) post.

Definition ret_pres (esp0:N) (mem:addr->N) (s:store) :=
  exists mem1, s V_MEM32 = Ⓜ mem1 /\ mem Ⓓ[ esp0 ] = mem1 Ⓓ[ esp0 ].

Definition my_prog_esp_ret_post (esp0:N) (mem:addr->N) (_:exit) (s:store) :=
  ret_pres esp0 mem s /\ s R_ESP = Ⓓ (esp0 ⊕ 4).

Definition my_prog_esp_ret_invset (esp0: N) (mem: addr -> N) :=
  trace_invs (my_prog_esp_ret_post esp0 mem).

Theorem my_prog_stack_preservation:
  forall s0 esp0 mem n s' x' (ESP0: s0 R_ESP = Ⓓ esp0)
  (MEM: s0 V_MEM32 = Ⓜ mem) (MDL0: models x86typctx s0)
  (RET0: my_prog s0 (mem Ⓓ[esp0]) = None)
  (WM: s0 A_WRITE = Ⓜ (fun _ => 1))
  (RM: s0 A_READ = Ⓜ (fun _ => 1))
  (XP0: exec_prog fh my_prog 0 s0 n s' x'),
  trueif_inv (my_prog_esp_ret_invset esp0 mem my_prog x' s').
Proof.
  intros.

  revert RET0. revert MDL0.

  induction on invariant XP0; intros. exact I.
  eapply preservation_exec_prog. exact MDL0. exact my_prog_welltyped. exact XP.

  einstantiate (checked_trace_program_steady_correct domain1 my_prog
    my_prog_jump_hints my_prog_ts fh 0) as TRACE.
    exact my_prog_nwc.
    reflexivity.
    eapply my_prog_hints_correct; try eassumption. reflexivity.

  unfold correct_trace_prog in TRACE.

  destruct_inv 32 PRE.

  all: x86_step; try exact I.

  einversion trivial (TRACE 34) as [δ [EQ HD] ]. inversion EQ. subst. clear EQ.

  concretize_delta HD V_MEM32. repeat split; try reflexivity;
  unfold mem_readable, mem_writable; psimpl; eexists;
  (split; [apply WM + apply RM|intro Contra; discriminate]).
  rewrite Hsv2 in Hsv. remember (2 ^ 32). inversion Hsv. subst.
  repeat unsimpl (setmem LittleE 4 _ _).

  concretize_delta HD R_ESP. reflexivity.
  apply nextinv_ret. psimpl.

  specialize (x86_regsize MDL0 ESP0) as ESP_BND.
  cbv beta match delta [x86typctx] in ESP_BND.

  assert (2 ^ 32 - 4 ⊕ esp0 < 2 ^ 32). apply N.mod_lt. discriminate.
  assert (2 ^ 32 - 4 + esp0 ⊕ 4294967292 < 2 ^ 32). apply N.mod_lt. discriminate.
  assert (4 <= absdist esp0 (2 ^ 32 + esp0 ⊖ 4)).
    erewrite N.add_sub_swap, <- modabsdist_eq_absdist, modr_modabsdist by trivial2.
    einversion trivial (modabsdist_add_l (2 ^ 32)) as [MAD|MAD];
        rewrite MAD; discriminate.
  assert (4 <= absdist esp0 (2 ^ 32 + esp0 - 4 ⊕ 4294967292)).
    erewrite N.add_sub_swap, <- modabsdist_eq_absdist, modr_modabsdist by trivial2.
    rewrite <- N.add_assoc, (N.add_comm esp0), N.add_assoc.
    einversion trivial (modabsdist_add_l (2 ^ 32)) as [MAD|MAD];
        rewrite MAD; discriminate.
  repeat split; try reflexivity; unfold mem_readable, mem_writable; psimpl;
  eexists; (split; [reflexivity|intro Contra; discriminate]).

  reflexivity.
  apply program


Theorem strchr_welltyped: welltyped_prog x86typctx strchr_i386.
Proof.
  Picinae_typecheck.
Qed.

Definition strchr_reachables_hint (ret: addr) (a: addr): option set :=
  match a with
  | 401 => Some {{ret}}
  | _ => None
  end.

Definition strchr_reachables ret := expand_reachables_fast_n
  (strchr_reachables_hint ret) strchr_i386 (0 :: nil, 0 :: nil) 100.

Definition strchr_trace_hint (p: program) (a: addr) (ts: trace_states):
  option (trace_states * bool) :=
  match a with
  | 401 => Some (ts, false)
  | _ => None
  end.

Require Extraction.
Extraction Language OCaml.

Definition strchr_trace reachables := expand_trace_program_n 100 (fun _ => true)
  strchr_trace_hint strchr_i386 reachables (tupdate_n treeN_nil 0 nil).

Definition strchr_trace2 reachables := expand_trace_program_n 100 domain1
  strchr_trace_hint strchr_i386 reachables (tupdate_n treeN_nil 0 nil).

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Require Import ExtrOcamlIntConv.
Extraction "calling" strchr_trace strchr_trace2 strchr_reachables list_to_set
  n_of_int int_of_n.

Goal True.
Proof.
  idtac "DOING STRCHR_TRACE".

  pose (x := strchr_reachables 0).
  compute in x.
  match eval compute in x with
  | Some (?v, nil) => clear x; pose (reachables := v)
  end.
  pose (x := strchr_trace2 (list_to_set reachables)).
  time (vm_compute in x). unbox_res x.

  pose (y := tget_n x 401); compute in y.

  pose (x := match strchr_trace reachables with
             | Some (ts, b) =>
                 match ts 401 with
                 | Some δ => Some (compactify_delta δ, b)
                 | None => None
                 end
             | None => None
             end).
  time (vm_compute in x).
  idtac "DONE COMPUTATION".
  match eval red in x with ?v => idtac v end.

  match eval red in x with
  | Some (?v, true) => idtac "STILL MORE"; clear x; pose (x := v)
  | Some (?v, false) => clear x; pose (x := v)
  end.
Abort.

  pose (vv2 := x V_MEM32). compute in vv2.





Compute
  match strchr_trace 1 with
  | Some (ts, b) => Some (ts 401, b)
  | None => None
  end.


Theorem strchr_preserves_ret:
  forall s esp0 mem n s' x' (ESP0: s R_ESP = Ⓓ esp0)
         (MDL0: models x86typctx s)
         (MEM: forall s, s V_MEM32 = Ⓜ mem)
         (RET0: strchr_i386 s (mem Ⓓ[esp0]) = None)
         (XP0: exec_prog fh strchr_i386 0 s n s' x'),
         trueif_inv (strchr_ret_invset esp0 mem strchr_i386 x' s').
Proof.
  intros.


  (* Trivial base case *)
  assert (Trivial:
    trueif_inv (strchr_ret_invset esp0 mem strchr_i386 (Exit 0) s)).
    exists mem. split. apply MEM. reflexivity.
  clear ESP0.

  (* TODO: this 0 should actually be some symbolic value (optimally)! *)
  compute_reaches 100 (strchr_reachables_hint 0) reachable XP0.

  (* Prove that the hint that we give is valid. *)
  unfold reachables_hint_correct. intros.
  destruct a_new as [|a]; repeat first [ discriminate | destruct a as [a|a|]].
  compute in LU. inversion LU. subst. clear dependent reachable.
  inversion Hints. subst. einstantiate trivial preservation_exec_prog as MDL.
  exact strchr_welltyped. step_stmt XS. destruct XS as [[ST' EX'] [? _]]. subst.
  inversion EX. subst. unsimpl (getmem LittleE 4 _ _). clear EX.
  (* Here we show that the return value is preserved!! *) admit.

  revert RET0 MDL0.
  induction on invariant XP0; intros.

  apply Trivial.

  (* MDL0 *)
  eapply preservation_exec_prog. exact MDL0. exact strchr_welltyped. exact XP.

  destruct_inv 32 PRE.

Abort.


(*
N.iter
Definition trace_program (ct: N) (c: typctx) (vars: list var) (p: program)
  (entry: addr) (fn: store_delta -> stmt -> trace_state_res_with_prop):
  option trace_states_prop :=
  let tsp := (update ⊥ entry (init_store_delta c), [entry], ⊥)
  match ct with
  | 0 => Some tsp
  | n
 *)

Definition reachable_thru h p a0 s0 a1 a' := exists s' n0 n1 s1,
  exec_prog h p a0 s0 n0 s1 (Exit a1) /\ exec_prog h p a1 s1 n1 s' (Exit a').

Definition has_delta' (s s': store) (δ: store_delta) (P: var -> option Prop) :=
  forall v val (ESE: eval_simple_exp s (δ v) val) (PP: true_hyp P v), s' v = val.

(* For all address in the delta store map, either we are reachable through the
 * working set, or the delta_stores are in fact correct for all possible
 * executions *)
Definition state_correctness h p a0 s0 fδ working conds := forall a1,
  (Exists (fun w => reachable_thru h p a0 s0 w a1) working) \/
  (forall s1 n1 δ (XP1: exec_prog h p a0 s0 n1 s1 (Exit a1))
    (LUdelta: fδ a1 = Some δ), has_delta' s0 s1 δ conds).

Theorem has_delta'_weaken: forall s s' δ P1 P2
  (IMP: forall v, true_hyp P2 v -> true_hyp P1 v)
  (HD': has_delta' s s' δ P1), has_delta' s s' δ P2.
Proof.
  unfold has_delta'. intros. apply IMP in PP. eapply HD'; try eassumption.
Qed.

Lemma reachable_exec_prog: forall h p a0 s0 a1 a'
  (Reach: reachable_thru h p a0 s0 a1 a'),
  exists s' n0 n1, exec_prog h p a0 s0 (n0 + n1) s' (Exit a').
Proof.
  unfold reachable_thru. intros. destruct Reach as [s' [n0 [n1 [s1 [XP1 XP2]]]]].
  repeat eexists. eapply exec_prog_concat; eassumption.
Qed.

(* Temporarily admit this, so that we can destruct on whether a *)
Axiom middle_excluded: forall P, P \/ not P.

Theorem trace_program_step_preserved_stmt: forall q sz h ts_fn vars p a0 s0 a
  next_states st' fδ fδ' δ working working' conds P'
  (SS: incl st' next_states)
  (NWC: forall s1 s2, p s1 = p s2)
  (* TODO: something for domain_complete *)
  (LUa: fδ a = Some δ) (TSQ: ts_fn δ q = Some (next_states, P'))
  (PA: p null_state a = Some (sz, q))
  (TP: trace_program_step vars p (fδ, (a :: working), conds) ts_fn =
    Some (fδ', working', h_conj conds P'))
  (IHfδ: state_correctness h p a0 s0 fδ (a :: working) conds),
  state_correctness h p a0 s0 fδ' working' (h_conj conds P').
Proof.
  induction next_states; intros; simpl in TP; rewrite PA, LUa, TSQ in TP;
  remember (fold_left _ _ _) as res eqn: TP2; destruct res as [fδ1' new_working];
  inversion TP; subst; clear TP; simpl in TP2.
  - (* nil *) inversion TP2. subst. unfold state_correctness in *. intros.
    pose (reachable2 := fun a2 a1 => reachable_thru h p a0 s0 a1 a2).
    destruct (IHfδ a1) as [Working_a1|HD'_a1].
    (* Exists in a::working *)
    + rewrite app_nil_r. inversion Working_a1 as [? ? Reach_a1|];
      [|left; assumption]. subst. destruct Reach_a1 as
        [s_a1 [n_0a [n_a_a1 [s_a [XP_0a XP_a_a1]]]]].
      (* Contradiction between XP_a_a1 and PA and TSQ *)
      admit.
    + (* Already correct *) right. intros. eapply has_delta'_weaken;
      try eapply HD'_a1; try eassumption. intros. unfold h_conj, true_hyp in *.
      destruct (conds v), (P' v); try destruct H; solve [reflexivity|assumption].
  - 

    simpl in TP2.
Admitted.
 *)

Theorem trace_program_step_preserved: forall vars ts_fn p a0 s0 fδ fδ' h
  working working' conds conds' (NWC: forall s1 s2, p s1 = p s2)
  (* TODO: something for domain_complete *)
  (TP: trace_program_step vars p (fδ, working, conds) ts_fn =
    Some (fδ', working', conds'))
  (IHfδ: state_correctness h p a0 s0 fδ working conds),
  state_correctness h p a0 s0 fδ' working' conds'.
Proof.
  intros. destruct working.
  - (* nil *) unfold state_correctness in *. intros. inversion TP. subst.
    destruct (IHfδ a1); (left + right); assumption.
  - (* a :: working' *) simpl in TP.
    destruct (p _ a) eqn: PA; [|inversion TP]. (* Is it a valid program address *)
    destruct p0 as [sz q]. destruct (fδ a) eqn: LUa; [|inversion TP].
    destruct (ts_fn _ _) eqn: TSQ; [|inversion TP]. destruct p0 as [next_states P'].
    remember (fold_left _ _ _) as res eqn: TP2. destruct res as [fδ1' new_working].
    inversion TP. subst. clear TP. eapply trace_program_step_preserved_stmt;
    try eassumption. simpl. rewrite PA, LUa, TSQ.
    rewrite <- TP2. reflexivity.
Qed.


Definition trace_program_def vars p tsp :=
  trace_program vars p tsp (fun δ q =>
    match simple_trace_stmt δ q with
    | Some x => Some (x, ⊥)
    | None => None
    end).

Definition get_reg v (ts: trace_state_res) :=
  match ts with
  | None => nil
  | Some (paths, _) => map (fun '(δ, _) => δ v) paths
  end.
Require Import strchr_i386.
Require Import fstat_i386.

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
      match stmt_reachable q with
      | Some jmps =>
          fold_left
          set_add jmps (a + sz)
      | None => None
  | None => None.

Fixpoint get_reachable (p: program) (a: addr) :=
  get_jumps
