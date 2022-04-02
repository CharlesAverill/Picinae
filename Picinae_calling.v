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

Require Import Picinae_core.
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

Module Type PICINAE_TRACING_DEFS (IL: PICINAE_IL).
  Import IL.
  Parameter absexp : Type.
  Parameter absenv : Type.

  Parameter absleb : absenv -> absenv -> bool.
  Parameter absle : absenv -> absenv -> Prop.

  Parameter absenv_init : absenv.
  Parameter absenv_bind : absenv -> var -> absexp -> absenv.
  Parameter absenv_meet : absenv -> absenv -> absenv.

  Parameter absexp_abstract : exp -> absenv -> absexp.
  Parameter absexp_models : hdomain -> store -> absexp -> value -> Prop.
  Parameter absexp_vals : absexp -> option (list value).

  Axiom absexp_models_eval :
    forall h st st' exp val aenv,
      (forall var,
          absexp_models h st (absexp_abstract (Var var) aenv) (st' var)) ->
      eval_exp h st' exp val ->
      absexp_models h st (absexp_abstract exp aenv) val.

  Axiom absenv_init_models :
    forall h st var,
      absexp_models h st (absexp_abstract (Var var) absenv_init) (st var).
  Axiom absenv_bind_models :
    forall h st v e1 e2 val a,
      absexp_models h st (absexp_abstract (Let v e1 e2) a) val ->
      absexp_models h
                    st
                    (absexp_abstract e2 (absenv_bind a v (absexp_abstract e1 a)))
                    val.
  Axiom absexp_vals_model :
    forall h st ae val l,
      absexp_vals ae = Some l -> In val l -> absexp_models h st ae val.

  Axiom absleb_absle : forall e1 e2, absleb e1 e2 = true <-> absle e1 e2.
  Axiom absle_trans : forall e1 e2 e3 (HE1 : absle e1 e2) (HE2 : absle e2 e3),
      absle e1 e3.
  Axiom absle_refl : forall e, absle e e.
  Axiom absle_meet_l : forall a1 a2, absle (absenv_meet a1 a2) a1.
  Axiom absle_meet_r : forall a1 a2, absle (absenv_meet a1 a2) a2.
  Axiom absle_models :
    forall h st e aenv1 aenv2 v,
      absle aenv1 aenv2 ->
      absexp_models h st (absexp_abstract e aenv2) v ->
      absexp_models h st (absexp_abstract e aenv1) v.
End PICINAE_TRACING_DEFS.

Module Type PICINAE_ABSEXP_ASSOC_DEFS (IL : PICINAE_IL).
  Import IL.
  Parameter absexp : Type.

  Parameter absexp_default : var -> absexp.
  Parameter absexp_meet : absexp -> absexp -> absexp.
  Parameter absexp_abstract : exp -> alist var absexp -> absexp.
  Parameter absexp_models : hdomain -> store -> absexp -> value -> Prop.
  Parameter absexp_vals : absexp -> option (list value).

  Parameter absexple : absexp -> absexp -> Prop.
  Parameter absexpleb : absexp -> absexp -> bool.

  Axiom absexp_models_eval :
    forall h st st' e val aenv,
      (forall v, absexp_models h st (absexp_abstract (Var v) aenv) (st' v)) ->
      eval_exp h st' e val ->
      absexp_models h st (absexp_abstract e aenv) val.

  Axiom absexp_nil_models :
    forall h st var,
      absexp_models h st (absexp_abstract (Var var) nil) (st var).

  Axiom absexp_bind_models :
    forall h st v e1 e2 val a,
      absexp_models h st (absexp_abstract (Let v e1 e2) a) val ->
      absexp_models h
                    st
                    (absexp_abstract e2 (assoc_cons v (absexp_abstract e1 a) a))
                    val.

  Axiom absexp_vals_model :
    forall h st ae val l,
      absexp_vals ae = Some l -> In val l -> absexp_models h st ae val.

  Axiom absexpleb_absexple : forall e1 e2, absexpleb e1 e2 = true <-> absexple e1 e2.
  Axiom absexple_trans :
    forall e1 e2 e3, absexple e1 e2 -> absexple e2 e3 -> absexple e1 e3.
  Axiom absexple_refl : forall e, absexple e e.
  Axiom absexple_meet_l : forall a1 a2, absexple (absexp_meet a1 a2) a1.
  Axiom absexple_meet_r : forall a1 a2, absexple (absexp_meet a1 a2) a2.
  Axiom absexple_meet_glb :
    forall a1 a2 al,
      absexple al a1 -> absexple al a2 -> absexple al (absexp_meet a1 a2).
  Axiom absexple_models :
    forall h st e1 e2 v,
      absexple e1 e2 -> absexp_models h st e2 v -> absexp_models h st e1 v.
  Axiom absexple_abstract :
    forall a1 a2 e,
      (forall v,
          absexple (assoc_def v a1 (absexp_default v))
                   (assoc_def v a2 (absexp_default v))) ->
      absexple (absexp_abstract e a1) (absexp_abstract e a2).
End PICINAE_ABSEXP_ASSOC_DEFS.

Module PICINAE_ABSEXP_ASSOC
       (IL : PICINAE_IL) (DEFS : PICINAE_ABSEXP_ASSOC_DEFS IL)
<: PICINAE_TRACING_DEFS IL.
  Import IL.

  Definition absexp := DEFS.absexp.
  Definition absenv := alist var absexp.

  Definition alookup v a :=
    match assoc v a with
    | Some x => x
    | None => DEFS.absexp_default v
    end.

  Definition absleb a1 a2 :=
    forallb (fun v => DEFS.absexpleb (alookup v a1) (alookup v a2))
            (map fst (a1 ++ a2)).
  Definition absle a1 a2 :=
    forall v, DEFS.absexple (alookup v a1) (alookup v a2).

  Definition absenv_init : absenv := nil.
  Definition absenv_bind a v e : absenv := assoc_cons v e a.
  Fixpoint absenv_meet' a1 a2 vars :=
    match vars with
    | nil => absenv_init
    | v::vs =>
        absenv_bind (absenv_meet' a1 a2 vs)
                    v
                    (DEFS.absexp_meet (alookup v a1) (alookup v a2))
    end.
  Definition absenv_meet a1 a2 := absenv_meet' a1 a2 (map fst (a1 ++ a2)).

  Definition absexp_abstract := DEFS.absexp_abstract.
  Definition absexp_models := DEFS.absexp_models.
  Definition absexp_vals := DEFS.absexp_vals.
  Definition absexp_models_eval := DEFS.absexp_models_eval.
  Definition absenv_init_models := DEFS.absexp_nil_models.
  Definition absenv_bind_models := DEFS.absexp_bind_models.
  Definition absexp_vals_model := DEFS.absexp_vals_model.

  Theorem absleb_absle e1 e2 : absleb e1 e2 = true <-> absle e1 e2.
  Proof.
    unfold absleb,absle.
    rewrite forallb_forall.
    split; intros HX v; specialize (HX v).
    {
      apply DEFS.absexpleb_absexple.
      rewrite map_app,in_app_iff in HX.
      unfold alookup in *.
      assert (HA1 := assoc_inx _ _ _ v e1).
      assert (HA2 := assoc_inx _ _ _ v e2).
      destruct assoc; [apply (in_map fst) in HA1;tauto|].
      destruct assoc; [apply (in_map fst) in HA2;tauto|].
      apply DEFS.absexpleb_absexple,DEFS.absexple_refl.
    }
    {
      intro HIn.
      apply DEFS.absexpleb_absexple.
      assumption.
    }
  Qed.

  Theorem absle_trans a1 a2 a3 (HL1 : absle a1 a2) (HL2 : absle a2 a3) :
    absle a1 a3.
  Proof.
    intro.
    eapply DEFS.absexple_trans; [apply HL1|apply HL2].
  Qed.

  Theorem absle_refl a : absle a a.
  Proof.
    intro.
    apply DEFS.absexple_refl.
  Qed.

  Theorem absle_models h st e a1 a2 val
             (HL : absle a1 a2)
             (HM : absexp_models h st (absexp_abstract e a2) val) :
    absexp_models h st (absexp_abstract e a1) val.
  Proof.
    eapply DEFS.absexple_models; [apply DEFS.absexple_abstract|]; eassumption.
  Qed.

  Theorem absenv_meet'_lookup a1 a2 v vl :
    alookup v (absenv_meet' a1 a2 vl) =
      if in_dec iseq v vl
      then DEFS.absexp_meet (alookup v a1) (alookup v a2)
      else DEFS.absexp_default v.
  Proof.
    destruct in_dec as [HIn|HNIn].
    {
      induction vl; simpl in *; [tauto|].
      unfold alookup,absenv_bind.
      rewrite assoc_cons_lookup.
      simpl.
      destruct iseq; subst; [reflexivity|].
      apply IHvl.
      destruct HIn; subst; tauto.
    }
    {
      induction vl; [reflexivity|].
      simpl.
      unfold alookup,absenv_bind.
      rewrite assoc_cons_lookup.
      simpl in *.
      destruct iseq; subst; tauto.
    }
  Qed.

  Theorem absle_meet_swap a1 a2 : absle (absenv_meet a1 a2) (absenv_meet a2 a1).
  Proof.
    intro v.
    unfold absenv_meet.
    repeat rewrite absenv_meet'_lookup,map_app.
    Search In app.
    do 2 destruct in_dec; repeat rewrite in_app_iff in *; try tauto;
    [|apply DEFS.absexple_refl].
    apply DEFS.absexple_meet_glb;
      [apply DEFS.absexple_meet_r|apply DEFS.absexple_meet_l].
  Qed.

  Theorem absle_meet_l a1 a2 : absle (absenv_meet a1 a2) a1.
  Proof.
    intro v.
    unfold absenv_meet.
    rewrite absenv_meet'_lookup.
    destruct in_dec as [_|HNIn]; [apply DEFS.absexple_meet_l|].
    assert (HA1 := assoc_inx _ _ _ v a1).
    unfold alookup.
    destruct assoc; [|apply DEFS.absexple_refl].
    apply (in_map fst) in HA1.
    rewrite map_app,in_app_iff in HNIn.
    tauto.
  Qed.

  Theorem absle_meet_r a1 a2 : absle (absenv_meet a1 a2) a2.
  Proof.
    eapply absle_trans; [apply absle_meet_swap|apply absle_meet_l].
  Qed.

  Theorem absle_meet_glb a1 a2 al (HL1 : absle al a1) (HL2 : absle al a2) :
    absle al (absenv_meet a1 a2).
  Proof.
    intro v.
    specialize (HL1 v).
    specialize (HL2 v).
    revert HL1 HL2.
    generalize (alookup v al).
    intros x HL1 HL2.
    unfold absenv_meet.
    rewrite absenv_meet'_lookup.
    destruct in_dec as [_|HNIn]; [apply DEFS.absexple_meet_glb;assumption|].
    assert (HA1 := assoc_inx _ _ _ v a1).
    assert (HA2 := assoc_inx _ _ _ v a2).
    rewrite map_app,in_app_iff in HNIn.
    unfold alookup in *.
    destruct assoc; [apply (in_map fst) in HA1|]; [tauto|].
    destruct assoc; [apply (in_map fst) in HA2|]; [tauto|].
    assumption.
  Qed.
End PICINAE_ABSEXP_ASSOC.

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

Module PICINAE_ABSEXP_OPTEXPEQ (IL : PICINAE_IL) <: PICINAE_ABSEXP_ASSOC_DEFS IL.
  Import IL.
  Definition absexp := option exp.
  Definition absexp_default v := Some (Var v).

  Program Instance exp_EqDec : EqDec exp.
  Next Obligation. Proof. decide equality; apply iseq. Defined.

  Fixpoint subst_exp e d : option exp :=
    match e with
    | Var v => assoc_def v d (Some (Var v))
    | Word _ _ => Some e
    | Load e1 e2 en len =>
        match subst_exp e1 d,subst_exp e2 d with
        | Some e1',Some e2' => Some (Load e1' e2' en len)
        | _,_ => None
        end
    | Store e1 e2 e3 en len =>
        match subst_exp e1 d,subst_exp e2 d,subst_exp e3 d with
        | Some e1',Some e2',Some e3' => Some (Store e1' e2' e3' en len)
        | _,_,_ => None
        end
    | BinOp op e1 e2 =>
        match subst_exp e1 d,subst_exp e2 d with
        | Some e1',Some e2' => Some (BinOp op e1' e2')
        | _,_ => None
        end
    | UnOp op e' =>
        match subst_exp e' d with
        | Some e'' => Some (UnOp op e'')
        | _ => None
        end
    | Cast typ w e' =>
        match subst_exp e' d with
        | Some e'' => Some (Cast typ w e'')
        | _ => None
        end
    | Let var val body =>
        subst_exp body (assoc_cons var (subst_exp val d) d)
    | Unknown _ => None
    | Ite e1 e2 e3 =>
        match subst_exp e1 d,subst_exp e2 d,subst_exp e3 d with
        | Some e1',Some e2',Some e3' => Some (Ite e1' e2' e3')
        | _,_,_ => None
        end
    | Extract n1 n2 e' =>
        match subst_exp e' d with
        | Some e'' => Some (Extract n1 n2 e'')
        | _ => None
        end
    | Concat e1 e2 =>
        match subst_exp e1 d,subst_exp e2 d with
        | Some e1',Some e2' => Some (Concat e1' e2')
        | _,_ => None
        end
    end.

  Definition absexp_abstract := subst_exp.
  Definition absexp_meet oe1 oe2 : absexp :=
    match oe1,oe2 with
    | Some e1,Some e2 => if e1 == e2 then Some e1 else None
    | _,_ => None
    end.

  Inductive eval_exp_na (s : store) : exp → value → Prop :=
    ENVar :
      forall v : var, eval_exp_na s (Var v) (s v)
  | ENWord :
    forall (n : N) (w : bitwidth), eval_exp_na s (Word n w) (VaN n w)
  | ENLoad :
    forall (e1 e2 : exp) (en : endianness) (len : N) (mw : bitwidth) (m : addr → N) (a : N),
      eval_exp_na s e1 (VaM m mw)
      → eval_exp_na s e2 (VaN a mw)
      → eval_exp_na s (Load e1 e2 en len) (VaN (getmem en len m a) (Mb * len))
  | ENStore :
    forall (e1 e2 e3 : exp) (en : endianness) (len : N) (mw : bitwidth) (m : addr → N) (a v : N),
      eval_exp_na s e1 (VaM m mw)
      → eval_exp_na s e2 (VaN a mw)
      → eval_exp_na s e3 (VaN v (Mb * len))
      → eval_exp_na s (Store e1 e2 e3 en len) (VaM (setmem en len m a v) mw)
  | ENBinOp :
    forall (bop : binop_typ) (e1 e2 : exp) (n1 n2 : N) (w : bitwidth),
      eval_exp_na s e1 (VaN n1 w)
      → eval_exp_na s e2 (VaN n2 w) → eval_exp_na s (BinOp bop e1 e2) (eval_binop bop w n1 n2)
  | ENUnOp :
    forall (uop : unop_typ) (e1 : exp) (n1 : N) (w1 : bitwidth),
      eval_exp_na s e1 (VaN n1 w1) → eval_exp_na s (UnOp uop e1) (eval_unop uop n1 w1)
  | ENCast :
    forall (ct : cast_typ) (w w' : bitwidth) (e1 : exp) (n : N),
      eval_exp_na s e1 (VaN n w) → eval_exp_na s (Cast ct w' e1) (VaN (cast ct w w' n) w')
  | ENLet :
    forall (v : var) (e1 e2 : exp) (u1 u2 : value),
      eval_exp_na s e1 u1 → eval_exp_na (s [v := u1]) e2 u2 → eval_exp_na s (Let v e1 e2) u2
  | ENUnknown :
    forall n w : N, n < 2 ^ w → eval_exp_na s (Unknown w) (VaN n w)
  | ENIte :
    forall (e1 e2 e3 : exp) (n1 : N) (w1 : bitwidth) (u' : value),
      eval_exp_na s e1 (VaN n1 w1)
      → eval_exp_na s match n1 with
                      | 0 => e3
                      | N.pos _ => e2
                      end u' → eval_exp_na s (Ite e1 e2 e3) u'
  | ENExtract :
    forall (w : bitwidth) (n1 n2 : N) (e1 : exp) (n : N),
      eval_exp_na s e1 (VaN n w)
      → eval_exp_na s (Extract n1 n2 e1) (VaN (xbits n n2 (N.succ n1)) (N.succ n1 - n2))
  | ENConcat :
    forall (e1 e2 : exp) (n1 : N) (w1 : bitwidth) (n2 : N) (w2 : bitwidth),
      eval_exp_na s e1 (VaN n1 w1)
      → eval_exp_na s e2 (VaN n2 w2)
      → eval_exp_na s (Concat e1 e2) (VaN (N.lor (N.shiftl n1 w2) n2) (w1 + w2)).

  Definition absexp_models (h : hdomain) s oe val :=
    match oe with
    | Some e => eval_exp_na s e val
    | None => True
    end.
  Definition absexp_vals oe :=
    match oe with
    | Some (Word n w) => Some (cons (VaN n w) nil)
    | _ => None
    end.
  Definition absexple (oe1 oe2 : absexp) :=
    match oe1,oe2 with
    | Some e1,Some e2 => e1 = e2
    | None,_ => True
    | Some _,None => False
    end.
  Definition absexpleb (oe1 oe2 : absexp) :=
    match oe1,oe2 with
    | Some e1,Some e2 => if e1 == e2 then true else false
    | None,_ => true
    | Some _,None => false
    end.

  Theorem eval_exp_na_degraded h s e val (HE : eval_exp h s e val) :
    eval_exp_na s e val.
  Proof.
    induction HE; econstructor; eassumption.
  Qed.

  Theorem absexp_models_eval h s s' e val a
          (HM : forall v, absexp_models h s (absexp_abstract (Var v) a) (s' v))
          (HE : eval_exp h s' e val) :
    absexp_models h s (absexp_abstract e a) val.
  Proof.
    unfold absexp_models.
    revert s a HM.
    induction HE; intros sx aenv HM; simpl.
    {
      apply HM.
    }
    7: {
      specialize (IHHE1 _ _ HM).
      apply IHHE2.
      simpl.
      unfold assoc_def.
      intro v'.
      rewrite assoc_cons_lookup.
      simpl.
      unfold update.
      destruct iseq; subst; [apply IHHE1|apply HM].
    }
    all:
      repeat match goal with
             | [IH : forall _ d _, match absexp_abstract ?e d with _ => _ end |- _] =>
                 specialize (IH _ _ HM)
             end.
    8: destruct n1.
    all:
      repeat match goal with
             | [|- context [match absexp_abstract _ _ with _ => _ end] ] =>
                 destruct absexp_abstract
             end; try solve [apply I].
    all: econstructor; eassumption.
  Qed.

  Theorem absexp_nil_models h st v :
      absexp_models h st (absexp_abstract (Var v) nil) (st v).
  Proof.
    constructor.
  Qed.

  Theorem absexp_bind_models h st v e1 e2 val a
      (HM : absexp_models h st (absexp_abstract (Let v e1 e2) a) val) :
    absexp_models h
                  st
                  (absexp_abstract e2 (assoc_cons v (absexp_abstract e1 a) a))
                  val.
  Proof.
    assumption.
  Qed.

  Theorem absexp_vals_model h st ae val l
          (HV : absexp_vals ae = Some l)
          (HIn : In val l) :
    absexp_models h st ae val.
  Proof.
    unfold absexp_vals in *.
    destruct ae as [e|]; [|discriminate].
    destruct e; try discriminate.
    inversion HV; subst.
    simpl in HIn.
    intuition; subst.
    constructor.
  Qed.

  Theorem absexpleb_absexple e1 e2 : absexpleb e1 e2 = true <-> absexple e1 e2.
  Proof.
    unfold absexpleb,absexple.
    destruct e1,e2; try solve [intuition].
    destruct iseq; subst; intuition.
  Qed.

  Theorem absexple_trans e1 e2 e3 (HL1 : absexple e1 e2) (HL2 : absexple e2 e3) :
    absexple e1 e3.
  Proof.
    unfold absexple in *.
    destruct e1,e2,e3; subst; tauto.
  Qed.

  Theorem absexple_refl oe : absexple oe oe.
  Proof.
    destruct oe; constructor.
  Qed.

  Theorem absexple_meet_l a1 a2 : absexple (absexp_meet a1 a2) a1.
  Proof.
    unfold absexple,absexp_meet.
    destruct a1,a2; try exact I.
    destruct iseq; subst; tauto.
  Qed.

  Theorem absexple_meet_r a1 a2 : absexple (absexp_meet a1 a2) a2.
  Proof.
    unfold absexple,absexp_meet.
    destruct a1,a2; try exact I.
    destruct iseq; subst; tauto.
  Qed.

  Theorem absexple_meet_glb a1 a2 al
          (HL1 : absexple al a1) (HL2 : absexple al a2) :
    absexple al (absexp_meet a1 a2).
  Proof.
    unfold absexple in *.
    destruct al,a1,a2; subst; try tauto.
    simpl.
    destruct iseq; tauto.
  Qed.

  Theorem absexple_models h st e1 e2 v
          (HL : absexple e1 e2) (HE : absexp_models h st e2 v) :
    absexp_models h st e1 v.
  Proof.
    destruct e1,e2; simpl in *; subst; tauto.
  Qed.

  Theorem absexple_abstract a1 a2 e
          (HA : forall v, absexple (assoc_def v a1 (absexp_default v))
                                   (assoc_def v a2 (absexp_default v))) :
    absexple (absexp_abstract e a1) (absexp_abstract e a2).
  Proof.
    unfold absexple.
    revert a1 a2 HA.
    induction e; simpl; intros a1 a2 HA.
    {
      apply HA.
    }
    7: {
      apply IHe2.
      intro v'.
      unfold absexple,assoc_def.
      repeat rewrite assoc_cons_lookup.
      simpl.
      destruct iseq; subst; [apply IHe1,HA|apply HA].
    }
    all: try tauto.
    all:
      repeat match goal with
               [ H :
                 forall _ _, _ -> match absexp_abstract ?e _ with _ => _ end |- _ ] =>
                 specialize (H _ _ HA);
                 destruct (absexp_abstract e a1),(absexp_abstract e a2);
                 subst; try tauto
             end; try tauto.
  Qed.
End PICINAE_ABSEXP_OPTEXPEQ.

Module PICINAE_CALLING (IL: PICINAE_IL) (DEFS : PICINAE_TRACING_DEFS IL).
  Import IL.
  Import DEFS.

  Inductive absexit := AELoc (n : N) | AEExp (e : exp) | AEExn (n : N).

  Definition trace_state : Type := absexit * absenv.

  Definition trace_state_step := option (list trace_state).

  Definition trace_result : Type := treeN absenv * list trace_state.
  Definition trace_inter : Type := trace_result * list trace_state.

  Definition join_res {A} res1 res2 : option (list A) :=
    match res1,res2 with
    | Some p1,Some p2 => Some (p1 ++ p2)
    | _,_ => None
    end.

  Fixpoint trace_stmt
           (q : stmt) (next : absenv -> trace_state_step) (d : absenv)
    : trace_state_step :=
    match q with
    | Nop => next d
    | Move v e => next (absenv_bind d v (absexp_abstract e d))
    | Jmp e => Some ((AEExp e,d) :: nil)
    | Exn n => Some ((AEExn n,d) :: nil)
    | Seq q1 q2 => trace_stmt q1 (trace_stmt q2 next) d
    | If _ q1 q2 => join_res (trace_stmt q1 next d) (trace_stmt q2 next d)
    | Rep _ s => None
    end.

  Definition trace_exit_res n d : trace_state_step := Some ((AELoc n,d)::nil).

  Definition step_trace prog '(info,r) '(ae,d) :=
    let skip := ((info,(ae,d)::r),nil) in
    match ae with
    | AELoc n =>
        match prog n with
        | None => skip
        | Some (sz,q) =>
            let odn := treeN_lookup info n in
            if match odn with
               | None => false
               | Some dx => absleb dx d
               end
            then ((info,r),nil)
            else let d' :=
                   match odn with
                   | None => d
                   | Some dx => absenv_meet d dx
                   end in
                 match trace_stmt q (trace_exit_res (n + sz)) d' with
                 | None => skip
                 | Some t => ((treeN_update info n (Some d'),r),t)
                 end
        end
    | _ => skip
    end.

  Definition absmodels h d st st' :=
    forall e val (HM : eval_exp h st' e val),
      absexp_models h st (absexp_abstract e d) val.

  Definition trace_state_models_exit h '(ax,d) st st' x :=
    absmodels h d st st' /\
      match ax,x with
      | AEExn n,Raise n'
      | AELoc n,Exit n' => n = n'
      | AEExp e',Exit n =>
          exists w, absexp_models h st (absexp_abstract e' d) (VaN n w)
      | _,_ => False
      end.

  Definition trace_state_models_oexit h P ts st st' ox :=
    match ox with
    | Some x => trace_state_models_exit h ts st st' x
    | None => P ts
    end.

  Definition trace_states_model h tsl st st' x :=
    Exists (fun ts => trace_state_models_exit h ts st st' x) tsl.

  Definition trace_states_modelo h P tsl st st' ox :=
    Exists (fun ts => trace_state_models_oexit h P ts st st' ox) tsl.

  Definition info_models_loc h info n st st' :=
    match treeN_lookup info n with
    | Some d => absmodels h d st st'
    | None => False
    end.

  Definition info_models_exit h info st st' x :=
    match x with
    | Raise _ => False
    | Exit n => info_models_loc h info n st st'
    end.

  Definition exec_inter_prog h p a st time1 st' a' time2 st'' x :=
    exec_prog h p a st time1 st' (Exit a') /\
      exec_prog h p a' st' time2 st'' x.

  Definition trace_result_models_exit h '(info,tsl) st st' x :=
    info_models_exit h info st st' x \/ trace_states_model h tsl st st' x.

  Definition trace_result_consistent h '(info,tsl) p st :=
    forall st' a st'' x sz q
           (HInfo : info_models_loc h info a st st')
           (HE : exec_stmt h st' q st'' x)
           (HP : p st' a = Some (sz,q)),
      trace_result_models_exit h (info,tsl) st st'' (exitof (a+sz) x).

  Definition trace_inter_consistent h '((info,tsl1),tsl2) p st :=
    trace_result_consistent h (info,tsl1 ++ tsl2) p st.

  (* Theorem absmodels_match h d st st' : *)
  (*   absmodels h d st st' <-> *)
  (*     forall v, *)
  (*       match d[[v]] with *)
  (*       | Some ev => eval_exp h st ev (st' v) *)
  (*       | None => True *)
  (*       end. *)
  (* Proof. *)
  (*   unfold absmodels. *)
  (*   split; intro HM; intro v; specialize (HM v). *)
  (*   { *)
  (*     destruct (d [[v]]); [|tauto]. *)
  (*     apply HM,eq_refl. *)
  (*   } *)
  (*   { *)
  (*     intros. *)
  (*     rewrite HX in HM. *)
  (*     assumption. *)
  (*   } *)
  (* Qed. *)

  Theorem absmodels_le h d1 d2 st st'
          (HL : absle d1 d2) (HM : absmodels h d2 st st') :
    absmodels h d1 st st'.
  Proof.
    unfold absmodels in *.
    intros ? ? HE.
    apply HM in HE.
    eapply absle_models; eassumption.
  Qed.

  Theorem trace_stmt_result' h P st st' st'' d q next ox
          (HD : absmodels h d st st')
          (HE : exec_stmt h st' q st'' ox)
          (HN : match ox with
                | None =>
                    forall d' (HND : absmodels h d' st st''),
                      match next d' with
                      | Some tsl' => Exists P tsl'
                      | None => True
                      end
                | Some x => True
                end) :
    match trace_stmt q next d with
    | Some tsl => trace_states_modelo h P tsl st st'' ox
    | None => True
    end.
  Proof.
    revert P st d next HD HN.
    unfold trace_states_modelo in *.
    induction HE; simpl in *; intros.
    {
      apply HN.
      assumption.
    }
    {
      apply HN.
      intros e' val HE.
      apply absenv_bind_models.
      eapply absexp_models_eval; [intro;apply HD;constructor|].
      econstructor; eassumption.
    }
    {
      constructor.
      simpl.
      split; [tauto|].
      exists w.
      eapply absexp_models_eval; [|eassumption].
      intro.
      apply HD.
      constructor.
    }
    {
      constructor.
      simpl.
      tauto.
    }
    {
      apply IHHE; assumption.
    }
    {
      eapply IHHE1; [apply HD|].
      intros.
      apply IHHE2; assumption.
    }
    {
      eapply IHHE in HD; [|apply HN].
      destruct c; do 2 destruct trace_stmt; try apply I;
        simpl; rewrite Exists_app; tauto.
    }
    {
      apply I.
    }
  Qed.

  Theorem trace_stmt_result h st st' st'' d q n ox tsl
          (HD : absmodels h d st st')
          (HE : exec_stmt h st' q st'' ox)
          (HTS: trace_stmt q (trace_exit_res n) d = Some tsl) :
    trace_states_model h tsl st st'' (exitof n ox).
  Proof.
    pose (P := fun ts => trace_state_models_exit h ts st st'' (Exit n)).
    assert
      (HX := trace_stmt_result' h P st st' st'' d q (trace_exit_res n) ox).
    rewrite HTS in HX.
    specialize (HX HD HE).
    destruct ox; apply HX; [tauto|].
    unfold P.
    simpl.
    intros.
    constructor.
    simpl.
    tauto.
  Qed.

  Theorem trace_result_consistent_exec h info tsl p a st st' time st'' x
          (HC : trace_result_consistent h (info,tsl) p st)
          (HInfo : info_models_loc h info a st st')
          (HE : exec_prog h p a st' time st'' x) :
    trace_result_models_exit h (info,tsl) st st'' x \/
      exists time1 time2 st'x a',
        time = (time1 + time2)%nat /\
          exec_prog h p a st' time1 st'x (Exit a') /\
          exec_prog h p a' st'x time2 st'' x /\
          trace_states_model h tsl st st'x (Exit a').
  Proof.
    revert HInfo.
    induction HE; simpl; [tauto| |]; intro.
    {
      assert (HCX := XS).
      eapply HC in HCX; [|eassumption].
      specialize (HCX LU).
      simpl in *.
      rewrite EX in *.
      simpl in HCX.
      destruct HCX as [HCX|HCX].
      {
        apply IHHE in HCX.
        destruct HCX as [|[? [? [? [? [? [? [? ?] ] ] ] ] ] ] ]; [tauto|].
        subst.
        right.
        eexists (S _).
        do 3 econstructor.
        repeat split; [|eassumption|eassumption].
        econstructor; eassumption.
      }
      {
        right.
        exists (S 0).
        simpl.
        do 3 econstructor.
        repeat split; [|eassumption|eassumption].
        econstructor; [| | |constructor]; eassumption.
      }
    }
    {
      eapply HC in XS; [|eassumption].
      apply XS in LU.
      left.
      assumption.
    }
  Qed.

  Theorem trace_result_consistent_init h tsl p st :
    trace_result_consistent h (treeN_nil,tsl) p st.
  Proof.
    simpl.
    intros.
    destruct a; compute in HInfo; tauto.
  Qed.

  Theorem trace_step_modelled h p st tn tsl tnd d n
          (HTN : treeN_lookup tn n = Some tnd)
          (HLE : absle tnd d)
          (HPrev : trace_result_consistent h (tn,(AELoc n,d)::tsl) p st) :
    trace_result_consistent h (tn,tsl) p st.
  Proof.
    unfold trace_result_consistent in *.
    intros.
    specialize (HPrev st' a st'' x sz q HInfo HE HP).
    unfold trace_result_models_exit,trace_states_model in *.
    rewrite Exists_cons in HPrev.
    destruct HPrev as [?|[HPrev|?] ]; [tauto| |tauto].
    unfold trace_state_models_exit in HPrev.
    destruct exitof eqn:HEX; [|tauto].
    destruct HPrev as [HPrev ?]; subst.
    simpl.
    unfold info_models_loc.
    rewrite HTN.
    left.
    eapply absmodels_le; eassumption.
  Qed.

  (* Theorem trace_state_models_exit_promote_word h d n w st st' x *)
  (*         (HM : trace_state_models_exit h (AEExp (Word n w)) st st' x) : *)
  (*   trace_state_models_exit h (d, AELoc n) st st' x. *)
  (* Proof. *)
  (*   simpl in *. *)
  (*   destruct HM as [? HM]. *)
  (*   split; [assumption|]. *)
  (*   destruct x; [|tauto]. *)
  (*   symmetry. *)
  (*   destruct HM as [? HM]. *)
  (*   inversion HM; subst. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Theorem trace_step_promote_word h p st tn tsl d n w *)
  (*         (HPrev : trace_result_consistent h (tn,(AEExp (Word n w),d)::tsl) p st) : *)
  (*   trace_result_consistent h (tn,(d,AELoc n)::tsl) p st. *)
  (* Proof. *)
  (*   unfold trace_result_consistent in *. *)
  (*   unfold trace_result_models_exit in *. *)
  (*   intros. *)
  (*   specialize (HPrev st' a st'' x sz q HInfo HE HP). *)
  (*   unfold trace_states_model in *. *)
  (*   rewrite Exists_cons in *. *)
  (*   destruct HPrev as [?|[HPrev|?] ]; [tauto| |tauto]. *)
  (*   right. *)
  (*   left. *)
  (*   eapply trace_state_models_exit_promote_word. *)
  (*   eassumption. *)
  (* Qed. *)

  Theorem trace_step_stmt_consistent h p st tn d tsl tsl' n sz q
          (dm := match treeN_lookup tn n with
                 | None => d
                 | Some d' => absenv_meet d d'
                 end)
          (HP : forall st' n, p st' n = p st n)
          (HTX : p st n = Some (sz,q))
          (HT : trace_stmt q (trace_exit_res (n + sz)) dm = Some tsl')
          (HPrev : trace_result_consistent h (tn,(AELoc n,d)::tsl) p st) :
    trace_inter_consistent h ((treeN_update tn n (Some dm),tsl),tsl') p st.
  Proof.
    unfold dm in *.
    clear dm.
    unfold trace_inter_consistent,trace_result_consistent in *.
    intros st' a st'' x sz' q' HInfo HE HPX.
    unfold trace_result_models_exit,trace_states_model in *.
    rewrite Exists_app.
    unfold info_models_loc in HInfo.
    rewrite treeN_lookup_update in HInfo.
    destruct (iseq n a) as [?|HX]; subst.
    {
      rewrite N.eqb_refl in HInfo.
      rewrite HP in HPX.
      rewrite HTX in HPX.
      inversion HPX; subst.
      right.
      right.
      eapply trace_stmt_result; eassumption.
    }
    {
      apply N.eqb_neq in HX.
      rewrite HX in HInfo.
      specialize (HPrev st' a st'' x sz' q' HInfo HE HPX).
      rewrite Exists_cons in HPrev.
      destruct HPrev as [HPrev|[HPrev|?] ]; [| |tauto].
      {
        left.
        destruct exitof as [a'|]; [|tauto].
        simpl in *.
        unfold info_models_loc in *.
        rewrite treeN_lookup_update.
        destruct (n =? a') eqn:HXX; [|assumption].
        apply Neqb_ok in HXX.
        subst.
        destruct (treeN_lookup tn a'); [|tauto].
        eapply absmodels_le; [|eassumption].
        apply absle_meet_r.
      }
      {
        left.
        simpl in *.
        destruct HPrev as [HM ?].
        destruct exitof; [subst|tauto].
        simpl in *.
        unfold info_models_loc.
        rewrite treeN_update_updated.
        destruct treeN_lookup; [|assumption].
        eapply absmodels_le; [|eassumption].
        apply absle_meet_l.
      }
    }
  Qed.

  Theorem trace_step_models_consistent h p st tn tsl ts
          (HP : forall st' n, p st' n = p st n)
          (HPrev : trace_result_consistent h (tn,ts::tsl) p st) :
    trace_inter_consistent h (step_trace (p st) (tn,tsl) ts) p st.
  Proof.
    assert (HSkip : trace_inter_consistent h ((tn,ts::tsl),nil) p st)
      by (simpl; rewrite app_nil_r; assumption).
    simpl.
    destruct ts as [ae d].
    destruct ae; [|assumption|assumption].
    destruct p as [ [? ?]|] eqn:HPX1; [|assumption].
    destruct (match treeN_lookup tn n with _ => _ end : bool) eqn:HL.
    {
      unfold trace_inter_consistent.
      rewrite app_nil_r.
      destruct treeN_lookup eqn:?; [|discriminate].
      apply absleb_absle in HL.
      eapply trace_step_modelled; eassumption.
    }
    {
      destruct trace_stmt eqn:HTR; [|assumption].
      eapply trace_step_stmt_consistent; eassumption.
    }
  Qed.
End PICINAE_CALLING.
