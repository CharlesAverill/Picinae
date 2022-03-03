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

Module Type PICINAE_CALLING_DEFS (IL: PICINAE_IL).
  Import IL.
  Parameter expleb : forall (e1 e2 : exp), bool.
  Parameter exple : forall (e1 e2 : exp), Prop.
  Axiom expleb_exple : forall e1 e2, expleb e1 e2 = true <-> exple e1 e2.
  Axiom exple_trans : forall e1 e2 e3 (HE1 : exple e1 e2) (HE2 : exple e2 e3),
      exple e1 e3.
  Axiom exple_refl : forall e, exple e e.
  Axiom eval_exple :
    forall h st e1 e2 v (HEq : exple e1 e2) (HE : eval_exp h st e2 v),
      eval_exp h st e1 v.
End PICINAE_CALLING_DEFS.

Module PICINAE_CALLING (IL: PICINAE_IL) (DEFS : PICINAE_CALLING_DEFS IL).
  Import IL.
  Import DEFS.
  Definition store_delta := alist var (option exp).

  Definition delta_lookup (l: store_delta) v : option exp :=
    match assoc v l with
    | Some (Some e) => Some e
    | Some None => None
    | None => Some (Var v)
    end.

  Notation "f [[ x := y ]]" :=
    (assoc_cons x y f) (at level 50, left associativity).

  Notation "f [[ v ]]" :=
    (delta_lookup f v) (at level 50, left associativity).

  Definition delta_merge_var oe1 oe2 :=
    match oe1,oe2 with
    | Some e1,Some e2 =>
        match expleb e1 e2,expleb e2 e1 with
        | true,_ => Some e1
        | _,true => Some e2
        | false,false => None
        end
    | None,_ | _,None => None
    end.

  Fixpoint delta_merge' (d1 d2 : store_delta) vl :=
    match vl with
    | nil => nil
    | v::vs => (delta_merge' d1 d2 vs) [[v:=delta_merge_var (d1[[v]]) (d2[[v]])]]
    end.

  Definition delta_merge (d1 d2 : store_delta) :=
    delta_merge' d1 d2 (map fst d1 ++ map fst d2).

  Definition delta_leb_var d1 d2 v :=
    match d1[[v]],d2[[v]] with
    | None,_ => true
    | Some _,None => false
    | Some e1,Some e2 => expleb e1 e2
    end.

  Definition delta_leb (d1 d2 : store_delta) :=
    forallb (fun v => delta_leb_var d1 d2 v) (map fst d1 ++ map fst d2).

  (*
    models exit as either 
    AELoc: a jump to n,
    AEExp: a value modelled by an expression (used for jumps, I think)
    AEExn: or a hardware exception
  *)
  Inductive absexit := AELoc (n : N) | AEExp (e : exp) | AEExn (n : N).

  (*
     the "delta" for an exit, associated with that exit in a tuple.
  *)
  Definition trace_state : Type := store_delta * absexit.

  (*
     literally "trace_state_result"
  *)
  Definition trace_state_res := option (list trace_state).

  Definition trace_result : Type := treeN store_delta * list trace_state.
  Definition trace_inter : Type := trace_result * list trace_state.

  (*
     I don't know why this is called join_res, I would call it join_option or something.
     it just joins two optional lists into a single optional list.
  *)
  Definition join_res {A} res1 res2 : option (list A) :=
    match res1,res2 with
    | Some p1,Some p2 => Some (p1 ++ p2)
    | _,_ => None
    end.

  Fixpoint subst_exp (d: store_delta) e : option exp :=
    match e with
    | Var v => d[[v]]
    | Word _ _ => Some e
    | Load e1 e2 en len =>
        match subst_exp d e1,subst_exp d e2 with
        | Some e1',Some e2' => Some (Load e1' e2' en len)
        | _,_ => None
        end
    | Store e1 e2 e3 en len =>
        match subst_exp d e1,subst_exp d e2,subst_exp d e3 with
        | Some e1',Some e2',Some e3' => Some (Store e1' e2' e3' en len)
        | _,_,_ => None
        end
    | BinOp op e1 e2 =>
        match subst_exp d e1,subst_exp d e2 with
        | Some e1',Some e2' => Some (BinOp op e1' e2')
        | _,_ => None
        end
    | UnOp op e' =>
        match subst_exp d e' with
        | Some e'' => Some (UnOp op e'')
        | _ => None
        end
    | Cast typ w e' =>
        match subst_exp d e' with
        | Some e'' => Some (Cast typ w e'')
        | _ => None
        end
    | Let var val body =>
        subst_exp (d[[var := subst_exp d val]]) body
    | Unknown _ => None
    | Ite e1 e2 e3 =>
        match subst_exp d e1,subst_exp d e2,subst_exp d e3 with
        | Some e1',Some e2',Some e3' => Some (Ite e1' e2' e3')
        | _,_,_ => None
        end
    | Extract n1 n2 e' =>
        match subst_exp d e' with
        | Some e'' => Some (Extract n1 n2 e'')
        | _ => None
        end
    | Concat e1 e2 =>
        match subst_exp d e1,subst_exp d e2 with
        | Some e1',Some e2' => Some (Concat e1' e2')
        | _,_ => None
        end
    end.

  Fixpoint trace_stmt
           (q : stmt) (next : store_delta -> trace_state_res) (d : store_delta)
    : trace_state_res :=
    match q with
    | Nop => next d
    | Move v e => next (d[[v := subst_exp d e]])
    | Jmp e =>
        match subst_exp d e with
        | Some e' => Some ((d,AEExp e') :: nil)
        | _ => None
        end
    | Exn n => Some ((d, AEExn n) :: nil)
    | Seq q1 q2 => trace_stmt q1 (trace_stmt q2 next) d
    | If _ q1 q2 => join_res (trace_stmt q1 next d) (trace_stmt q2 next d)
    | Rep _ s => None
    end.

  Definition trace_exit_res n d : trace_state_res := Some ((d,AELoc n)::nil).

  (*less than or equal to relationship for option deltas*)
  Definition odelta_leb od1 od2 :=
    match od1,od2 with
    | Some d1,Some d2 => delta_leb d1 d2
    | None,Some _ => false
    | _,None => true
    end.

  Definition odelta_merge d1 od2 :=
    match od2 with
    | Some d2 => delta_merge d1 d2
    | None => d1
    end.

  (*
     prog: prog
      -- the program we're stepping through

     info: treeN store_delta 
      -- association between addresses and store_deltas.
     r: list (trace_state)
      -- this isn't used outside of setp_trace, i can only assume that its intent is to catalogue all the deltas for instructions we cannot model
       - for instance, if we jump out of the program, we (None => skip match below) we just add our asserted delta d to the response list.
       - in other words, I believe its used to catalogue values for exits.
    (info, r) : trace_result


     d:  store_delta
      -- the delta we are asserting for this current address
    ae: absexit
      -- the value inside this exit points us to instruction we're analyzing. it must be an AELoc.
    (d, ae): trace_state 

     return value: (option store_delta) * treeP store_delta * list (trace_state) * list (trace_state)
     -->  trace_result *  list trace_state 
     -- list trace_state is a list places that the address we're looking at exits to and their associated new deltas.
    where: 
      Type trace_state := (store_delta * absexit)
      Type treeN store_delta := (option store_delta) * (treeP store_delta)
        the first element of the tuple is the 0th element of the tree, per the definition of 
  *)
  Definition step_trace prog '(info,r) '(d,ae) :=
    let skip := ((info,(d,ae)::r),nil) in
    match ae with
    | AELoc n =>
        match prog n with
        | None => skip
        | Some (sz,q) =>
            let odn := treeN_lookup info n in
            if odelta_leb odn (Some d)
            then ((info,r),nil) (*if the existing delta in info is (less than or equal to ) (that is
                                  to say, consistent) with the one we are asserting, then keep that one.*)
                                (*otherwise, recalculate...*)
            else let d' := odelta_merge d odn in (*otherwise, we merge the deltas.*)
                 match trace_stmt q (trace_exit_res (n + sz)) d' with
                 | None => skip
                 | Some t => ((treeN_update info n (Some d'),r),t)
                 end
        end
    | _ => skip
    end.

  Definition promote (tsl : list (trace_state)) :=
    fold_left  (fun acc '(d,ae) =>
        match ae with
        | AEExp (Word n w) => (d, AELoc n)::acc
        | _ => (d,ae)::acc
        end
      ) tsl nil.
  Definition trace_prog_accum_func prog '(a_info, a_ts) ts :=
      let (a_info', n_ts):= (step_trace prog a_info ts) in
      let n_ts_promote := promote n_ts in
      (a_info',n_ts_promote++a_ts).

  Definition trace_prog prog '((info,r), tsl)  :=
    let trace_prog_accum_func0 := trace_prog_accum_func prog in
    fold_left trace_prog_accum_func0 tsl ((info,r), nil).

  Definition delta_le (d1 d2 : store_delta) := 
    forall v e (HV : d1[[v]] = Some e),
    exists e', d2[[v]] = Some e' /\ exple e e'.

  Definition delta_eq d1 d2 := delta_le d1 d2 /\ delta_le d2 d1.

  (* Definition delta_models h d st st' := *)
  (*   forall v ev val (HX : d[[v]] = Some ev) (HME : eval_exp h st ev val), *)
  (*     st' v = val. *)

  (*
    (h : hdomain) 
    (d : store_delta)
    (st : store)
    (st' : store)

    FORALL: (v : var) (ev : exp) (val : value)
    SUCH THAT "d" (which is an associative list from vars to expressions, similar to how it
     was in calling_int) has  Some expression "ev" in it for variable "v",
    AND evaluating "ev" under "h" and "st" yields "val",
    IT FOLLOWS THAT st' v = val.

    In simple terms, this proposition holds if all the delta expressions in d model the variable changes
     between st and st'.
  *)
  Definition delta_models h d st st' :=
    forall v ev (HX : d[[v]] = Some ev), eval_exp h st ev (st' v).

  (*
     (h : hdomain) 
    '(d : store_delta
     , ax : absexit)
    (st : store)
    (st' : store)
    (x : exit)
  *)
  Definition trace_state_models_exit h '(d,ax) st st' x :=
    delta_models h d st st' /\
      match ax,x with
      | AEExn n,Raise n'
      | AELoc n,Exit n' => n = n'
      | AEExp e',Exit n =>
          exists w, eval_exp h st e' (VaN n w)
      | _,_ => False
      end.

  Definition trace_state_models_oexit h P ts st st' ox :=
    match ox with
    | Some x => trace_state_models_exit h ts st st' x
    | None => P ts
    end.

  (*
    trace_states_model holds IF
      there exists an element "ts" of tsl for which trace_state_models_exit holds
  *)
  Definition trace_states_model h tsl st st' x :=
    Exists (fun ts => trace_state_models_exit h ts st st' x) tsl.

  Definition trace_states_modelo h P tsl st st' ox :=
    Exists (fun ts => trace_state_models_oexit h P ts st st' ox) tsl.

  (*
     this holds if there is a delta store for n that models the difference between st and st'
   *)
  Definition info_models_loc h info n st st' :=
    match treeN_lookup info n with
    | Some d => delta_models h d st st'
    | None => False
    end.

  Definition info_models_exit h info st st' x :=
    match x with
    | Raise _ => False
    | Exit n => info_models_loc h info n st st'
    end.

  (*
     exec_inter_prog holds IF 
      there is some path of execution in p from address a to time1  that exits to a'
      there is some path of execution in p from address a' to time2  that ends in st''
      nothing uses this.
  *)
  Definition exec_inter_prog h p a st time1 st' a' time2 st'' x :=
    exec_prog h p a st time1 st' (Exit a') /\
      exec_prog h p a' st' time2 st'' x.

  (*
     either x exits into an address covered by info, and info has a delta that models st->st',
     or x jumps into an address covered by tsl and the delta store for that address in tsl covers it.
   *)
  Definition trace_result_models_exit h '(info,tsl) st st' x :=
    info_models_exit h info st st' x \/ trace_states_model h tsl st st' x.

  (*
    (h : hdomain) 
    '(info, tsl) 
    (p : (var → value) → N → option (N * stmt)) 
      (aka p : program)
    (st : store)

    trace_result_consistent holds IF:
    FORALL (st' : var → value) (a : N) (st'' : store) (x : option exit) 
      (sz : N) (q : stmt)
    SUCH THAT
      -> HInfo: "info" delta_store for address "a" models the difference between st and st'
      -> HE: executing instruction "q" with store "st'" yields st'' and exit x,
      -> HP: instruction "q" is at address "a" in program "p" with size "sz"
    IT FOLLOWS THAT
      -> either x exits into an address covered by info, and info has a delta that models st->st'',
       or x jumps into an address covered by tsl and the delta store for that address in tsl covers it.
  *)
  Definition trace_result_consistent h '(info,tsl) p st :=
    forall st' a st'' x sz q
           (HInfo : info_models_loc h info a st st')
           (HE : exec_stmt h st' q st'' x)
           (HP : p st' a = Some (sz,q)),
      trace_result_models_exit h (info,tsl) st st'' (exitof (a+sz) x).

  (*This exists since step_trace returns deltas for unexplored or unresolved addresses in tsl2.*)
  Definition trace_inter_consistent h '((info,tsl1),tsl2) p st :=
    trace_result_consistent h (info,tsl1 ++ tsl2) p st.

  Theorem delta_le_match d1 d2 :
    delta_le d1 d2 <->
      forall v,
        match d1[[v]],d2[[v]] with
        | Some e1,Some e2 => exple e1 e2
        | Some _,None => False
        | None,_ => True
        end.
  Proof.
    unfold delta_le.
    split; intros HX v; specialize (HX v).
    {
      destruct (d1 [[v]]);[|tauto].
      destruct (HX _ eq_refl) as [? [HEq ?] ].
      rewrite HEq.
      assumption.
    }
    {
      intros e HV.
      rewrite HV in HX.
      destruct (d2 [[v]]); [|tauto].
      econstructor; split; [reflexivity|eassumption].
    }
  Qed.

  Theorem delta_le_leb d1 d2 (HL : delta_leb d1 d2 = true) : delta_le d1 d2.
  Proof.
    unfold delta_le,delta_leb,delta_leb_var,delta_lookup in *.
    intros v e HV.
    rewrite forallb_app in HL.
    rewrite andb_true_iff in HL.
    repeat rewrite forallb_forall in HL.
    destruct HL as [HL1 HL2].
    specialize (HL1 v).
    specialize (HL2 v).
    destruct (assoc v d1) as [ [?|]|] eqn:HA1;
      [|discriminate|]; inversion HV; subst.
    {
      apply assoc_in in HA1.
      apply (in_map fst) in HA1.
      apply HL1 in HA1.
      destruct (assoc v d2) as [ [?|]|] eqn:HA2; [|discriminate|];
        econstructor; (split; [reflexivity|apply expleb_exple; eassumption]).
    }
    {
      destruct (assoc v d2) as [o|] eqn:HA2.
      {
        apply assoc_in in HA2.
        apply (in_map fst) in HA2.
        apply HL2 in HA2.
        destruct o; [|discriminate].
        apply expleb_exple in HA2.
        econstructor; (split; [reflexivity|eassumption]).
      }
      {
        econstructor; (split; [reflexivity|]).
        apply exple_refl.
      }
    }
  Qed.

  Theorem delta_leb_le d1 d2 (HL : delta_le d1 d2) : delta_leb d1 d2 = true.
  Proof.
    unfold delta_le,delta_leb,delta_leb_var in *.
    rewrite forallb_forall.
    intros v HIn.
    specialize (HL v).
    destruct (d1 [[v]]); [|reflexivity].
    destruct (HL _ eq_refl) as [? [HX ?] ].
    rewrite HX.
    apply expleb_exple.
    assumption.
  Qed.

  Theorem delta_le_trans d1 d2 d3 (HL1 : delta_le d1 d2) (HL2 : delta_le d2 d3) :
    delta_le d1 d3.
  Proof.
    unfold delta_le in *.
    intros v e HV.
    edestruct HL1 as [? [? ?] ]; [eassumption|].
    edestruct HL2 as [? [? ?] ]; [eassumption|].
    econstructor; split; [|eapply exple_trans]; eassumption.
  Qed.

  Theorem delta_le_refl d : delta_le d d.
  Proof.
    intros v e HV.
    exists e.
    split; [eassumption|apply exple_refl].
  Qed.

  Theorem delta_lookup_cons d v x k :
    d [[v := x]] [[k]] = if k == v then x else d [[k]].
  Proof.
    unfold delta_lookup.
    rewrite assoc_cons_lookup.
    simpl.
    destruct iseq; [|reflexivity].
    destruct x; reflexivity.
  Qed.

  Theorem expleb_dest e1 e2 :
    if expleb e1 e2 then exple e1 e2 else ~exple e1 e2.
  Proof.
    destruct expleb eqn:HX; rewrite <- expleb_exple,HX; [tauto|discriminate].
  Qed.

  Theorem delta_merge'_in d1 d2 vl v (HIn : In v vl) :
    delta_merge' d1 d2 vl [[v]] = delta_merge_var (d1 [[v]]) (d2 [[v]]).
  Proof.
    induction vl; simpl in HIn; [tauto|].
    simpl.
    rewrite delta_lookup_cons.
    destruct iseq; subst; [tauto|].
    apply IHvl.
    destruct HIn; [|assumption].
    subst.
    tauto.
  Qed.

  Theorem delta_merge'_notin' d1 d2 vl v (HNIn : ~In v vl) :
    assoc v (delta_merge' d1 d2 vl) = None.
  Proof.
    induction vl; [reflexivity|].
    simpl in *.
    rewrite assoc_remove_lookup.
    destruct iseq; subst; tauto.
  Qed.

  Theorem delta_merge'_notin d1 d2 vl v (HNIn : ~In v vl) :
    (delta_merge' d1 d2 vl) [[v]] = Some (Var v).
  Proof.
    unfold delta_lookup.
    rewrite delta_merge'_notin' by assumption.
    reflexivity.
  Qed.

  Theorem delta_merge'_lookup d1 d2 vl v :
    (delta_merge' d1 d2 vl) [[v]] =
      if in_dec iseq v vl
      then delta_merge_var (d1 [[v]]) (d2 [[v]])
      else Some (Var v).
  Proof.
    destruct in_dec; [apply delta_merge'_in|apply delta_merge'_notin];
      assumption.
  Qed.

  Theorem delta_merge_lookup d1 d2 v :
    delta_merge d1 d2 [[v]] = delta_merge_var (d1 [[v]]) (d2 [[v]]).
  Proof.
    unfold delta_merge.
    rewrite delta_merge'_lookup.
    destruct in_dec as [|HX]; [reflexivity|].
    unfold delta_merge_var.
    unfold delta_lookup.
    rewrite in_app_iff in HX.
    apply Decidable.not_or in HX.
    destruct HX as [HX1 HX2].
    destruct (assoc v d1) as [|] eqn:HA1;
      [apply assoc_in,(in_map fst) in HA1; tauto|].
    destruct (assoc v d2) as [|] eqn:HA2;
      [apply assoc_in,(in_map fst) in HA2; tauto|].
    assert (HD := expleb_dest (Var v) (Var v)).
    destruct expleb; [reflexivity|].
    destruct HD.
    apply exple_refl.
  Qed.

  Theorem delta_merge_symm d1 d2 :
    delta_le (delta_merge d1 d2) (delta_merge d2 d1).
  Proof.
    rewrite delta_le_match.
    intro v.
    repeat rewrite delta_merge_lookup.
    unfold delta_merge_var.
    destruct (d1 [[v]]) as [e1|],(d2 [[v]]) as [e2|]; try exact I.
    assert (HX1 := expleb_dest e1 e2).
    assert (HX2 := expleb_dest e2 e1).
    do 2 destruct expleb; apply exple_refl + tauto.
  Qed.

  Theorem delta_merge_le_l d1 d2 :
    delta_le (delta_merge d1 d2) d1.
  Proof.
    rewrite delta_le_match.
    intro v.
    rewrite delta_merge_lookup.
    destruct (d1 [[v]]) as [e1|]; simpl; [|exact I].
    destruct (d2 [[v]]) as [e2|]; simpl; [|exact I].
    assert (HX1 := expleb_dest e1 e2).
    assert (HX2 := expleb_dest e2 e1).
    do 2 destruct expleb; apply exple_refl + tauto.
  Qed.

  Theorem delta_merge_le_r d1 d2 :
    delta_le (delta_merge d1 d2) d2.
  Proof.
    eapply delta_le_trans; [apply delta_merge_symm|apply delta_merge_le_l].
  Qed.

  (* Theorem delta_merge_glb d1 d2 dx (HL1 : delta_le dx d1) (HL2 : delta_le dx d2) : *)
  (*   delta_le dx (delta_merge d1 d2). *)
  (* Proof. *)
  (*   unfold delta_le in *. *)
  (*   intros v e HV. *)
  (*   specialize (HL1 v e HV). *)
  (*   specialize (HL2 v e HV). *)
  (*   clear dx HV. *)
  (*   unfold delta_merge. *)
  (*   destruct HL1 as [? [HD1 HL1X] ], HL2 as [? [HD2 HL2X] ]. *)
  (*   destruct (in_dec iseq v (map fst d1 ++ map fst d2)) as [HX|HX]. *)
  (*   { *)
  (*     apply (delta_merge'_in d1 d2) in HX. *)
  (*     rewrite HD1,HD2 in HX. *)
  (*     destruct (delta_merge' _ _ _ [[v]]); destruct HX. *)
  (*     { *)
  (*       econstructor. *)
  (*       split; [reflexivity|]. *)
  (*       eapply exple_trans; [apply HL1X|]. *)
  (*       apply exple_symm. *)
  (*       assumption. *)
  (*     } *)
  (*     { *)
  (*       eapply exple_trans; [|eassumption]. *)
  (*       apply exple_symm. *)
  (*       assumption. *)
  (*     } *)
  (*   } *)
  (*   { *)
  (*     rewrite delta_merge'_notin by assumption. *)
  (*     econstructor. *)
  (*     split; [reflexivity|]. *)
  (*     unfold delta_lookup in HD1. *)
  (*     destruct assoc eqn:HIn; [|inversion HD1; subst; assumption]. *)
  (*     destruct HX. *)
  (*     apply in_or_app. *)
  (*     apply assoc_in in HIn. *)
  (*     apply (in_map fst) in HIn. *)
  (*     left. *)
  (*     assumption. *)
  (*   } *)
  (* Qed. *)

  (* Theorem delta_models_match h d st st' : *)
  (*   delta_models h d st st' <-> *)
  (*     forall v, *)
  (*       match d[[v]] with *)
  (*       | Some ev => eval_exp h st ev (st' v) *)
  (*       | None => True *)
  (*       end. *)
  (* Proof. *)
  (*   unfold delta_models. *)
  (*   split; intros HM v; specialize (HM v); *)
  (*     [|intros ? HX; rewrite HX in HM; assumption]. *)
  (*   destruct (d [[v]]); [|exact I]. *)
  (*   apply HM,eq_refl. *)
  (* Qed. *)

  (* Theorem delta_models_le h d1 d2 st st' *)
  (*         (HL : delta_le d1 d2) (HM : delta_models h d2 st st') : *)
  (*   delta_models h d1 st st'. *)
  (* Proof. *)
  (*   rewrite delta_models_match in *. *)
  (*   intro v. *)
  (*   rewrite delta_le_match in HL. *)
  (*   specialize (HM v). *)
  (*   specialize (HL v). *)
  (*   destruct (d1 [[v]]); [|exact I]. *)
  (*   destruct (d2 [[v]]); [|destruct HL]. *)
  (*   eapply eval_exple. *)
  (*   unfold delta_models in *. *)
    
  (* Qed. *)

  Theorem delta_models_match h d st st' :
    delta_models h d st st' <->
      forall v,
        match d[[v]] with
        | Some ev => eval_exp h st ev (st' v)
        | None => True
        end.
  Proof.
    unfold delta_models.
    split; intro HM; intro v; specialize (HM v).
    {
      destruct (d [[v]]); [|tauto].
      apply HM,eq_refl.
    }
    {
      intros.
      rewrite HX in HM.
      assumption.
    }
  Qed.

  Theorem delta_models_le h d1 d2 st st'
          (HL : delta_le d1 d2) (HM : delta_models h d2 st st') :
    delta_models h d1 st st'.
  Proof.
    rewrite delta_models_match,delta_le_match in *.
    intro.
    specialize (HM v).
    specialize (HL v).
    destruct (d1 [[v]]); [|apply I].
    destruct (d2 [[v]]); [|tauto].
    intros.
    eapply eval_exple; eassumption.
  Qed.

  Theorem subst_exp_model' h d s s' e val
          (HST : delta_models h d s s')
          (HE1 : eval_exp h s' e val) :
    match subst_exp d e with
    | Some e' => eval_exp h s e' val
    | None => True
    end.
  Proof.
    rewrite delta_models_match in *.
    revert d s HST.
    induction HE1; simpl; intros.
    1: {
      apply HST.
    }
    7: {
      apply IHHE1_2.
      intro v'.
      rewrite delta_lookup_cons in *.
      destruct iseq; subst; [|rewrite update_frame by assumption; apply HST].
      rewrite update_updated.
      apply IHHE1_1.
      assumption.
    }
    all:
      repeat match goal with
             | [IH : forall d _ _, match subst_exp d ?e with _ => _ end |- _] =>
                 specialize (IH _ _ HST)
             end.
    8: destruct n1.
    all:
      repeat match goal with
             | [|- context [match subst_exp _ _ with _ => _ end] ] =>
                 destruct subst_exp
             end; try solve [apply I].
    all: econstructor; try eassumption.
    all: try (econstructor; eassumption).
  Admitted.

  Theorem subst_exp_model h d s s' e val e'
          (HST : delta_models h d s s')
          (HS : subst_exp d e = Some e')
          (HE1 : eval_exp h s' e val) :
    eval_exp h s e' val.
  Proof.
    eapply subst_exp_model' in HE1; [|eassumption].
    rewrite HS in *.
    assumption.
  Qed.

  Theorem trace_stmt_result' h P st st' st'' d q next ox
          (HD : delta_models h d st st')
          (HE : exec_stmt h st' q st'' ox)
          (HN : match ox with
                | None =>
                    forall d' (HND : delta_models h d' st st''),
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
      rewrite delta_models_match in *.
      intros v'.
      rewrite delta_lookup_cons in *.
      destruct iseq; subst; [|rewrite update_frame by assumption; apply HD].
      rewrite update_updated.
      eapply subst_exp_model'; [|eassumption].
      apply delta_models_match.
      assumption.
    }
    {
      destruct subst_exp eqn:HS; [|tauto].
      constructor.
      simpl.
      split; [assumption|].
      exists w.
      eapply subst_exp_model; eassumption.
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
          (HD : delta_models h d st st')
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

  (*
    GIVEN THAT,
      HC: 
      HInfo:
      HE: there's some execution path of "time" steps to exit x
    IT FOLLOWS THAT 
      EITHER (info,tsl) models the change from st to st'' to x
      or there's some intermediate execution in those "time" number of steps that is modelled by tsl.

     this is interesting, but is not the proof nor definition of correctness needed for trace_prog.
     i think what we need is basically this, but without the OR qualifier in the conclusion.
      
      This is not used by anything.
  *)
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
          (HLE : delta_le tnd d)
          (HPrev : trace_result_consistent h (tn,(d,AELoc n)::tsl) p st) :
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
    eapply delta_models_le; eassumption.
  Qed.

  Theorem trace_state_models_exit_promote_word h d n w st st' x
          (HM : trace_state_models_exit h (d, AEExp (Word n w)) st st' x) :
    trace_state_models_exit h (d, AELoc n) st st' x.
  Proof.
    simpl in *.
    destruct HM as [? HM].
    split; [assumption|].
    destruct x; [|tauto].
    symmetry.
    destruct HM as [? HM].
    inversion HM; subst.
    reflexivity.
  Qed.

  Theorem trace_step_promote_word h p st tn tsl d n w
          (HPrev : trace_result_consistent h (tn,(d,AEExp (Word n w))::tsl) p st) :
    trace_result_consistent h (tn,(d,AELoc n)::tsl) p st.
  Proof.
    unfold trace_result_consistent in *.
    unfold trace_result_models_exit in *.
    intros.
    specialize (HPrev st' a st'' x sz q HInfo HE HP).
    unfold trace_states_model in *.
    rewrite Exists_cons in *.
    destruct HPrev as [?|[HPrev|?] ]; [tauto| |tauto].
    right.
    left.
    eapply trace_state_models_exit_promote_word.
    eassumption.
  Qed.

  Theorem trace_step_stmt_consistent h p st tn d tsl tsl' n sz q
          (od' := treeN_lookup tn n)
          (dm := odelta_merge d od')
          (HP : forall st' n, p st' n = p st n) (*code is non-modifiable*)
          (HTX : p st n = Some (sz,q))
          (HT : trace_stmt q (trace_exit_res (n + sz)) dm = Some tsl')
          (HPrev : trace_result_consistent h (tn,(d,AELoc n)::tsl) p st) :
    trace_inter_consistent h ((treeN_update tn n (Some dm),tsl),tsl') p st.
  Proof.
    unfold dm,od' in *.
    clear dm od'.
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
        eapply delta_models_le; [|eassumption].
        apply delta_merge_le_r.
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
        eapply delta_models_le; [|eassumption].
        apply delta_merge_le_l.
      }
    }
  Qed.
  (*
     Theorem:
     IF 
     -> HP: code is non-self-modifying
     -> HPrev for every address in the program p that has an address q, there is an element of
     ts::tsl that models the exit and change of executing that statement (this is a bad definition but it works)
     IT FOLLOWS THAT
     -> step_trace preserves that, or something.
  *)  

  Theorem trace_step_models_consistent h p st tn tsl ts
          (HP : forall st' n, p st' n = p st n) (*code is non-modifible*)
          (HPrev : trace_result_consistent h (tn,ts::tsl) p st) :
    trace_inter_consistent h (step_trace (p st) (tn,tsl) ts) p st.
  Proof.
    assert (HSkip : trace_inter_consistent h ((tn,ts::tsl),nil) p st)
      by (simpl; rewrite app_nil_r; assumption).
    simpl.
    destruct ts as [d ae].
    destruct ae; [|assumption|assumption].
    destruct p as [ [? ?]|] eqn:HPX1; [|assumption].
    destruct odelta_leb eqn:HL.
    {
      unfold trace_inter_consistent.
      rewrite app_nil_r.
      unfold odelta_leb in HL.
      destruct treeN_lookup eqn:?; [|discriminate].
      apply delta_le_leb in HL.
      eapply trace_step_modelled; eassumption.
    }
    {
      destruct trace_stmt eqn:HTR; [|assumption].
      eapply trace_step_stmt_consistent; eassumption.
    }
  Qed.

  Theorem eval_exple_altdef_bad h st
          (exple : forall e1 e2, Prop)
          (* (exple_symm : forall e1 e2, exple e1 e2 -> exple e2 e1) *)
          (exple_refl : forall e, exple e e)
          (* (exple_trans : *)
          (*   forall e1 e2 e3, exple e1 e2 -> exple e2 e3 -> exple e1 e3) *)
          (eval_exple :
            forall e1 e2 v1 v2
                   (HEq : exple e1 e2)
                   (HE1 : eval_exp h st e1 v1)
                   (HE2 : eval_exp h st e2 v2),
              v1 = v2) :
    False.
  Proof.
    specialize (eval_exple (Unknown 1) _ (VaN 0 1) (VaN 1 1) (exple_refl _)).
    assert (HX : VaN 0 1 <> VaN 1 1) by (intro BAD; inversion BAD).
    apply HX,eval_exple; constructor; reflexivity.
  Qed.

  Theorem trace_prog_complete:
    forall h a_0 st_0 st_1 n st_n info info' r r' tsl x (prog: program)
    (H1: ((info',r'), nil) = trace_prog (prog st_0) ((info,r),tsl))
    (H2: info_models_loc h info' a_0 st_0 st_1) 
    (H3: exec_prog h prog a_0 st_1 n st_n x)
    (HP : forall st_e1 st_e2 n_e, prog st_e1 n_e = prog st_e2 n_e),
    trace_result_models_exit h (info',r') st_0 st_n x.
  Proof.
  Admitted.
End PICINAE_CALLING.

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

Module PICINAE_CALLING_DEFS_EQ (IL : PICINAE_IL) <: PICINAE_CALLING_DEFS IL.
  Import IL.

  Program Instance exp_EqDec: EqDec exp.
  Next Obligation. Proof. decide equality; apply iseq. Defined.

  Definition exple (e1 e2 : exp) := e1 = e2.
  Definition expleb e1 e2 := if e1 == e2 then true else false.
  Theorem expleb_exple e1 e2 : expleb e1 e2 = true <-> exple e1 e2.
  Proof.
    unfold expleb,exple.
    destruct iseq; intuition.
  Qed.
  Theorem exple_trans e1 e2 e3 (HEq1 : exple e1 e2) (HEq2 : exple e2 e3) :
    exple e1 e3.
  Proof.
    unfold exple in *.
    subst.
    reflexivity.
  Qed.
  Definition exple_refl (e : exp) := eq_refl e.
  Theorem eval_exple h st e1 e2 v (HEq : exple e1 e2) (HE : eval_exp h st e2 v) :
    eval_exp h st e1 v.
  Proof.
    unfold exple in *.
    subst.
    assumption.
  Qed.
End PICINAE_CALLING_DEFS_EQ.
