Require Import Picinae_core.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import ZArith.
Open Scope list_scope.

Theorem unk_bound (n w:N): n mod 2^w < 2^w.
Proof. apply N.mod_lt, N.pow_nonzero. discriminate 1. Qed.

Module Type PSIMPL_EXPS_DEFS (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL).
Import IL.
Import TIL.
Import FIL.

Module Type M := PSIMPL_DEFS_V1_1 IL TIL FIL.
Include M.

(* Exps can translate to either numeric or memory sasts. *)
Inductive sastNM :=
  ASTNum (a:sastN) (w:bitwidth) | ASTMem (a:sastM) (w:bitwidth).

Definition simpl_sastNM t e :=
  match e with
  | ASTNum e' w => ASTNum (simpl_sastN t e') w
  | ASTMem e' w => ASTMem (simpl_sastM t e') w
  end.

(* The mvtree nodes must contain Coq terms returning the actual values of the
   IL variables v.  These terms typically have the form (s v) where s is a
   Coq proof variable (and therefore unexpandable).  However, we need to at
   least be able to fully expand the IL type of v in order to create the
   correct kind of node.  To solve this problem, our exp simplifier will take
   "universal stores" (ustores) as input, and we will provide the user a
   mechanism for converting an (unexpandable) store and an (expandable)
   typing context into a ustore.  Ustores return None for untyped variables,
   and Some u for typed variables, where u is a uvalue whose type fields
   are fully expandable (though its values fields are not). *)
Definition ustore := var -> option uvalue.

(* Since we can't actually expand the values, the user must supply a proof
   that the values in the ustore are actually bounded by the bitwidths in
   the (expandable) type fields.  We here define ustore_boundedness, and
   we will later supply a theorem that the user can use to create one of these
   from a store and typing context. *)
Definition uvalue_boundedness (u:uvalue) :=
  match u with VaU z m n w => if z then n < 2^w else welltyped_memory m end.
Definition ouvalue_boundedness (ou:option uvalue) :=
  match ou with None => True | Some u => uvalue_boundedness u end.
Definition ustore_boundedness (us:var -> option uvalue) :=
  forall v, ouvalue_boundedness (us v).

Fixpoint lookup {A B : Type} {EQD:EqDec A} (var : A) (kvl:list (A*B)) : option B :=
  match kvl with
  | cons (k,val) kvs => if iseq var k then Some val else lookup var kvs
  | nil => None
  end.

Theorem mvt_lookup_insert t v d : mvt_lookup (mvt_insert t v d) v = d.
Proof.
  revert t.
  induction v; destruct t; simpl; auto.
Qed.

Lemma mvt_lookup_insert_frame:
  forall id1 id2 t mvd (NE: id1 <> id2),
  mvt_lookup (mvt_insert t id1 mvd) id2 = mvt_lookup t id2.
Proof.
  intros.
  revert id1 t mvd NE.
  induction id2; destruct id1,t; simpl; auto;
    try tauto; intros; rewrite IHid2; auto; intro; subst; tauto.
Qed.

Section Exp2Sast.

(* Inputs: *)

(* a ustore created from a store and typing context *)
Variable us : var -> option uvalue.

(* a proof of boundedness for f created from a proof that c models s *)
Variable USB : ustore_boundedness us.

(* Convert an exp to an sastN or sastM.  Inputs:
   us: ustore (constructed using ustore_of_store)
   USB: proof of ustore boundedness (construted using make_ustore_boundedness)
   t: initially MVT_Empty
   e: IL expression to convert

   Outputs:
   None = Conversion failed because e is not well-typed or contains something
          that cannot be represented as an sast.  We cannot simplify those.
   Some (t',a) = Sast "a" evaluated in context t' denotes the same set of values
                 as expression e evaluated in context us. *)
Definition typ_lookup (c : list (var * option typ)) v :=
  match lookup v c with | Some (Some t) => Some t | _ => None end.

Fixpoint exp2sast (e:exp) (env:list (var * sastNM)) {struct e}
  : option sastNM :=
  let rec := fun e => exp2sast e env in
  match e with
  | Var v => lookup v env
  | Unknown _ => None
  | Word n w => Some (ASTNum (SIMP_Const n) w)
  | Load e1 e2 en len =>
      match rec e1 with Some (ASTMem a1 w) =>
      match rec e2 with Some (ASTNum a2 _) =>
        Some (ASTNum (SIMP_GetMem en len a1 a2) (Mb * len))
      | _ => None end | _ => None end
  | Store e1 e2 e3 en len =>
      match rec e1 with Some (ASTMem a1 w) =>
      match rec e2 with Some (ASTNum a2 _) =>
      match rec e3 with Some (ASTNum a3 _) =>
        Some (ASTMem (SIMP_SetMem en len a1 a2 a3) w)
      | _ => None end | _ => None end | _ => None end
  | Let v e1 e2 =>
    match rec e1 with
    | Some a1 => exp2sast e2 ((v,a1)::env)
    | _ => None
    end
  | BinOp op e1 e2 =>
    match rec e1,rec e2 with
    | Some (ASTNum a1 w),Some (ASTNum a2 _) =>
        let xw := fun x => Some (ASTNum x w) in
        let xb :=
          fun x =>
            Some (ASTNum (SIMP_IteBN x (SIMP_Const 1) (SIMP_Const 0)) 1) in
        let xnb :=
          fun x =>
            Some (ASTNum (SIMP_IteBN x (SIMP_Const 0) (SIMP_Const 1)) 1) in
        let ww := (SIMP_Const (2^w)) in
        let mw := fun x => xw (SIMP_Mod x ww) in
        match op with
        | OP_PLUS => mw (SIMP_Add a1 a2)
        | OP_MINUS => mw (SIMP_Sub (SIMP_Add ww a1) a2)
        | OP_TIMES => mw (SIMP_Mul a1 a2)
        | OP_DIVIDE => None
        | OP_SDIVIDE => None
        | OP_MOD => xw (SIMP_Mod a1 a2)
        | OP_SMOD => None
        | OP_LSHIFT => mw (SIMP_ShiftL a1 a2)
        | OP_RSHIFT => xw (SIMP_ShiftR a1 a2)
        | OP_ARSHIFT => None
        | OP_AND => xw (SIMP_LAnd a1 a2)
        | OP_OR => xw (SIMP_LOr a1 a2)
        | OP_XOR => xw (SIMP_Xor a1 a2)
        | OP_EQ => xb (SIMP_Eqb a1 a2)
        | OP_NEQ => xnb (SIMP_Eqb a1 a2)
        | OP_LT => xb (SIMP_Ltb a1 a2)
        | OP_LE => xnb (SIMP_Ltb a2 a1)
        | OP_SLT => None
        | OP_SLE => None
      end
    | _,_ => None
    end
  | UnOp op e' =>
      match op with
      | OP_NEG => None
      | OP_NOT => None
      end
  | Cast op w e' =>
      match op with
      | CAST_LOW => None
      | CAST_HIGH => None
      | CAST_SIGNED => None
      | CAST_UNSIGNED => None
      end
  | Ite e1 e2 e3 =>
      match rec e1,rec e2,rec e3 with
      | Some (ASTNum a1 _),Some (ASTNum a2 w2),Some (ASTNum a3 w3) =>
          if w2 == w3 then Some (ASTNum (SIMP_IteNN a1 a2 a3) w2) else None
      | Some (ASTNum a1 _),Some (ASTMem a2 w2),Some (ASTMem a3 w3) =>
          if w2 == w3 then Some (ASTMem (SIMP_IteNM a1 a2 a3) w2) else None
      | _,_,_ => None
      end
  | Extract n1 n2 e' => None
  | Concat e1 e2 => None
  end.

Inductive eval_sastNM (t:metavar_tree) : sastNM -> value -> Prop :=
| EvNum a n w (H: eval_sastN t a = n): eval_sastNM t (ASTNum a w) (VaN n w)
| EvMem a m w (H: eval_sastM t a = m): eval_sastNM t (ASTMem a w) (VaM m w).

Theorem exp2sast_sound e env h st t v :
  (forall v,
      match lookup v env with
      | Some x => eval_sastNM t x (st v)
      | None => True
      end) ->
  (* models (typ_lookup c) st -> *)
  eval_exp h st e v ->
  match exp2sast e env with
  | Some x => eval_sastNM t x v
  | None => True
  end.
Proof.
  intros HEnv HEv.
  revert env HEnv.
  induction HEv; intros; simpl.
  1: { apply HEnv. }
  7: {
    (* This is the Let case *)
    specialize (IHHEv1 env HEnv).
    destruct exp2sast; [|tauto].
    apply IHHEv2.
    intro k.
    specialize (HEnv k).
    simpl.
    destruct iseq; [|rewrite update_frame; assumption].
    subst.
    rewrite update_updated.
    assumption.
  }
  5: destruct uop.
  7: destruct ct.
  all: try tauto.
  5: destruct n1.
  all: repeat match goal with
              | [ H : (forall env', _ -> match exp2sast ?e env' with | _ => _ end) |-
                  context [ exp2sast ?e ?env ] ] =>
                specialize (H env)
              end; intuition.
  all: repeat match goal with
              | [ |- context [match exp2sast ?e ?env with | _ => _ end] ] =>
                destruct (exp2sast e env) as [[?|?]|]; try tauto
              end.
  all: repeat match goal with
              | [ H : eval_sastNM _ (ASTNum _ _) _ |- _ ] => inversion H; subst; clear H
              | [ H : eval_sastNM _ (ASTMem _ _) _ |- _ ] => inversion H; subst; clear H
              end.
  5-8: destruct (_ == _); subst; [|tauto].
  4: destruct bop.
  all: try solve [constructor; tauto].
  {
    constructor.
    simpl.
    destruct (_ =? _); reflexivity.
  }
  {
    constructor.
    simpl.
    unfold N.ltb,N.leb.
    rewrite N.compare_antisym.
    destruct (_ ?= _); reflexivity.
  }
  all: constructor; simpl; try rewrite H1; try rewrite H2; reflexivity.
Qed.

Fixpoint getvars' e acc : list var :=
  match e with
  | Var v =>
    match List.find (fun x => if iseq v x then true else false) acc with
    | None => cons v acc
    | Some _ => acc
    end
  | Word _ _ => acc
  | Load e1 e2 _ _ => getvars' e2 (getvars' e1 acc)
  | Store e1 e2 e3 _ _ => (getvars' e3 (getvars' e2 (getvars' e1 acc)))
  | BinOp _ e1 e2 => getvars' e2 (getvars' e1 acc)
  | UnOp _ e' => getvars' e' acc
  | Cast _ _ e' => getvars' e' acc
  | Let _ e1 e2 => getvars' e2 (getvars' e1 acc)
  | Unknown _ => acc
  | Ite e1 e2 e3 => (getvars' e3 (getvars' e2 (getvars' e1 acc)))
  | Extract _ _ e' => getvars' e' acc
  | Concat e1 e2 => getvars' e2 (getvars' e1 acc)
  end.

Definition getvars e := getvars' e nil.

Definition e2s_mvard'' (u:uvalue) (UVB: uvalue_boundedness u) : metavar_data.
  destruct u as [[|] m n w].
  { exact (MVNum n (SIMP_BND w UVB)). }
  { exact (MVMem m (Some UVB)). }
Defined.

Definition e2s_mvard' (u:option uvalue) : ouvalue_boundedness u -> option metavar_data :=
  match u with
  | Some u' => fun UVB => Some (e2s_mvard'' u' UVB)
  | None => fun _ => None
  end.

Definition e2s_mvard v := e2s_mvard' (us v) (USB v).
Definition mvdtyp d : option typ :=
  match d with
  | MVNum _ (SIMP_BND n _) => Some (NumT n)
  | MVMem _ (Some WTM) => Some (MemT Mb)
  | _ => None
  end.

Definition mvexpr v n :=
  match us v with
  | Some (VaU b _ _ w) =>
    Some (if b
          then (ASTNum (SIMP_NVar n 0 SIMP_UBND 0 SIMP_UBND) w)
          else (ASTMem (SIMP_MVar n zeromem None zeromem None) w))
  | None => None
  end.

Definition plength {A} (l : list A) := Pos.of_succ_nat (length l).

Fixpoint build_varpos_slow (l : list var) : list (var * positive) :=
  match l with
  | cons v vs => (v,plength vs) :: build_varpos_slow vs
  | nil => nil
  end.

Fixpoint build_varpos (l : list var) : list (var * positive) :=
  match l with
  | nil => nil
  | cons v vs =>
    let rest := build_varpos vs in
    match rest with
    | cons (_,p) _ => (v,Pos.succ p) :: rest
    | nil => (v,xH) :: nil
    end
  end.

Theorem build_varpos_slowdown l : build_varpos l = build_varpos_slow l.
Proof.
  induction l; auto.
  simpl.
  rewrite IHl.
  destruct l; auto.
Qed.

Fixpoint init_env (l : list (var * positive)) : option (list (var * sastNM)) :=
  match l with
  | cons (v,p) xs =>
    match init_env xs, mvexpr v (N.pos p) with
    | Some rest,Some x => Some ((v,x) :: rest)
    | None,_ | _,None => None
    end
  | nil => Some nil
  end.

Definition build_env l := init_env (build_varpos l).

Fixpoint build_mvt_slow (l : list var) : option metavar_tree :=
  match l with
  | cons v vs =>
    match build_mvt_slow vs,e2s_mvard v with
      | None,_ | _,None => None
      | Some t,Some d => Some (mvt_insert t (plength vs) d)
    end
  | nil => Some MVT_Empty
  end.

Fixpoint build_mvt' (l : list var) : option (positive * metavar_tree) :=
  match l with
  | cons v vs =>
    match build_mvt' vs,e2s_mvard v with
      | None,_ | _,None => None
      | Some (p,t),Some d => Some (Pos.succ p,mvt_insert t p d)
    end
  | nil => Some (xH,MVT_Empty)
  end.

Definition build_mvt l := option_map snd (build_mvt' l).

Theorem build_mvt_slowdown' l :
  match build_mvt' l with
  | None => build_mvt_slow l = None
  | Some (p,t) => p = plength l /\ build_mvt_slow l = Some t
  end.
  induction l; simpl; auto.
  destruct build_mvt' as [[? ?]|]; [|rewrite IHl]; auto.
  edestruct IHl as [? HX].
  subst.
  rewrite HX.
  destruct e2s_mvard; tauto.
Qed.

Theorem build_mvt_slowdown l : build_mvt l = build_mvt_slow l.
Proof.
  assert (HX := build_mvt_slowdown' l).
  unfold build_mvt.
  destruct build_mvt' as [[? ?]|]; simpl; auto.
  symmetry.
  tauto.
Qed.

Theorem build_env_max l v t n d env e val :
  (length l <= n)%nat ->
  build_env l = Some env ->
  lookup v env = Some e ->
  eval_sastNM (mvt_insert t (Pos.of_succ_nat n) d) e val <->
  eval_sastNM t e val.
Proof.
  revert n env.
  unfold build_env.
  rewrite build_varpos_slowdown.
  induction l; intros n env HL HEnv HA; [inversion HEnv; subst; discriminate|].
  simpl in *.
  unfold mvexpr in HEnv.
  destruct init_env; [|discriminate].
  destruct us as [[z ? ? ?]|]; [|discriminate].
  inversion HEnv; subst.
  simpl in *.
  destruct iseq; [|eapply IHl; eauto using le_Sn_le].
  inversion HA; subst.
  assert (Pos.of_succ_nat n <> plength l).
  {
    intro HX.
    unfold plength in *.
    apply SuccNat2Pos.inj in HX.
    subst.
    apply Nat.nle_succ_diag_l in HL.
    assumption.
  }
  destruct z; split; intro HX; inversion HX; subst;
    constructor; simpl; rewrite mvt_lookup_insert_frame; auto.
Qed.

Theorem build_env_lookup_us l v :
  match build_env l with
  | Some env =>
    match lookup v env with
      | Some _ => exists y, us v = Some y
      | None => True
    end
  | None => True
  end.
Proof.
  unfold build_env.
  rewrite build_varpos_slowdown.
  induction l; simpl; auto.
  destruct init_env; auto.
  unfold mvexpr.
  destruct (us a) as [[? ? ? ?]|] eqn:?; auto.
  simpl.
  destruct iseq; subst; eauto.
Qed.

Theorem build_mvt_env_works l v :
  match build_mvt l,build_env l with
  | Some t,Some env =>
    match lookup v env,us v with
    | Some x,Some u => eval_sastNM t x (of_uvalue u)
    | None,_ | _,None => True
    end
  | None,_ | _,None => True
  end.
Proof.
  unfold build_env in *.
  rewrite build_varpos_slowdown,build_mvt_slowdown.
  induction l; simpl; auto.
  assert (HM := build_env_max l v).
  unfold build_env in *.
  rewrite build_varpos_slowdown in *.
  simpl in *.
  unfold e2s_mvard,e2s_mvard',mvexpr.
  generalize (USB a).
  intro.
  destruct build_mvt_slow,init_env,(us a) as [[z ? ? ?]|] eqn:HU; auto.
  simpl.
  destruct iseq; subst.
  {
    rewrite HU.
    destruct z; constructor; simpl; rewrite mvt_lookup_insert; reflexivity.
  }
  {
    destruct lookup eqn:HX; auto.
    destruct (us v) as [[[|] ? ? ?]|]; auto; eapply HM; eauto.
  }
Qed.
End Exp2Sast.

End PSIMPL_EXPS_DEFS.


Module Type PSIMPL_EXPS_SIG
  (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL).

Import IL.
Import TIL.
Import FIL.
Include PSIMPL_EXPS_DEFS IL TIL FIL.

(* Here's the mechanism we provide for converting stores and typing contexts into
   ustores.  We want ustore_of_store to expand during computations, but not
   val_to_uval, so the latter's definition is hidden here. *)

Parameter val_to_uval: store -> var -> typ -> uvalue.

Definition ustore_of_store (c:typctx) (s:store) : var -> option uvalue :=
  fun v => option_map (val_to_uval s v) (c v).

Parameter make_ustore_boundedness:
  forall (c:typctx) (s:store) (MDL:models c s), ustore_boundedness (ustore_of_store c s).

(* Then we need the main soundness proof.  I think it looks like
   the following, but I'm not sure. *)

End PSIMPL_EXPS_SIG.


Module PSimpl_Exps
  (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL) : PSIMPL_EXPS_SIG IL TIL FIL.

Import IL.
Import TIL.
Import FIL.
Include PSIMPL_EXPS_DEFS IL TIL FIL.
Module PTheory := PicinaeTheory IL.
(* Module PSimp := Picinae_Simplifier_v1_1 IL TIL FIL. *)
Import SIL.
Import PTheory.
Import List.

(* This should be generalized and never expanded at computation time. *)
Definition val_to_uval (s:store) (v:var) (_:typ) :=
  match s v with VaN n w => VaU true zeromem n w
               | VaM m w => VaU false m 0 w end.

Definition ustore_of_store (c:typctx) (s:store) : var -> option uvalue :=
  fun v => option_map (val_to_uval s v) (c v).

Theorem make_ustore_boundedness (c:typctx) (s:store) (MDL:models c s):
  ustore_boundedness (ustore_of_store c s).
Proof.
  unfold ustore_boundedness, ustore_of_store, val_to_uval. intro v.
  specialize (MDL v). destruct (c v).
    specialize (MDL _ (eq_refl _)). inversion MDL.
      exact LT.
      exact WTM.
    exact I.
Qed.

Theorem exp2sast_soundgen' h c s MDL e vars x :
  let us := ustore_of_store c s in
  let USB := make_ustore_boundedness c s MDL in
  eval_exp h s e x ->
  match build_mvt us USB vars,build_env us vars with
  | Some t,Some env =>
    match exp2sast e env with
    | Some e' => eval_sastNM t e' x
    | None => True
    end
  | None,_ | _,None => True
  end.
Proof.
  intros.
  assert (HL := build_env_lookup_us us vars).
  assert (HX := build_mvt_env_works us USB vars).
  unfold us,USB in *.
  clear us USB.
  destruct build_mvt; auto.
  destruct build_env eqn:HE; auto.
  eapply exp2sast_sound; eauto.
  intro.
  specialize (HX v).
  specialize (HL v).
  destruct lookup; auto.
  destruct HL.
  unfold ustore_of_store,val_to_uval,option_map in *.
  destruct c; [|discriminate].
  destruct s; auto.
Qed.

Theorem exp2sast_soundgen h c s MDL e x :
  let vars := getvars e in
  let us := ustore_of_store c s in
  let USB := make_ustore_boundedness c s MDL in
  eval_exp h s e x ->
  match build_mvt us USB vars,build_env us vars with
  | Some t,Some env =>
    match exp2sast e env with
    | Some e' => eval_sastNM t e' x
    | None => True
    end
  | None,_ | _,None => True
  end.
Proof.
  intro.
  apply exp2sast_soundgen'.
Qed.

Theorem eval_sastNM_simpl t e x (HE : eval_sastNM t e x) :
  eval_sastNM t (simpl_sastNM t e) x.
Proof.
  destruct e; inversion HE; subst; constructor.
Qed.

End PSimpl_Exps.
