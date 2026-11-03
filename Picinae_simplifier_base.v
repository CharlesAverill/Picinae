(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2026 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
   Expression simplifier:                            MMMMMMMMMMMZMDMD77$.ZMZMM78
   * auto-simplifies expressions faster than          MMMMMMMMMMMMMMMMMMMZOMMM+Z
     applying series of Coq tactics by leveraging      MMMMMMMMMMMMMMMMM^NZMMN+Z
     reflective ltac programming                        MMMMMMMMMMMMMMM/.$MZM8O+
   * This module merely defines the core interface       MMMMMMMMMMMMMM7..$MNDM+
     for all simplifiers.  For the code that actually     MMDMMMMMMMMMZ7..$DM$77
     implements simplification, see each simplifier        MMMMMMM+MMMZ7..7ZM~++
     module (e.g., Picinae_simplifier_v1_1.v).              MMMMMMMMMMM7..ZNOOMZ
                                                             MMMMMMMMMM$.$MOMO=7
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

From Stdlib Require Import NArith.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Require Import Picinae_core.
Require Import Picinae_finterp.

(* Ltac1 callers may pass a hypothesis as an identifier (hyp notation), a
   variable term, or a named introduction pattern (e.g. a name used by set).
   Accept all three without interpreting other introduction patterns as names. *)
Ltac2 picinae_hyp_ident (h : Ltac1.t) :=
  match Ltac1.to_ident h with
  | Some id => id
  | None =>
      match Ltac1.to_constr h with
      | Some term =>
          match Constr.Unsafe.kind term with
          | Constr.Unsafe.Var id => id
          | _ => Control.zero (Tactic_failure (Some
              (Message.of_string "Expected a hypothesis")))
          end
      | None =>
          match Ltac1.to_intro_pattern h with
          | Some (Std.IntroNaming (Std.IntroIdentifier id)) => id
          | _ => Control.zero (Tactic_failure (Some
              (Message.of_string "Expected a hypothesis")))
          end
      end
  end.

(* This file defines the central tactic notations that launch Picinae's auto-
   simplification process for symbolic expressions yielded by the IL interperter.
   Since different proofs (and even different steps within a single proof) often
   require different styles of auto-simplification, and we wish to retain
   backwards compatibility for older proofs designed to use older versions of
   the simplifier, we define these tactic notations as dispatchers of a
   secondary tactic "PSimplifier" that can be redefined by the user to activate
   different simplifiers as desired.  Example:

   Ltac PSimplifier ::= PSimplifier_v1_0.
   (* Henceforth the interpreter's "step" tactic will use simplifier v1.0. *)
   Ltac PSimplifier ::= PSimplifier_v2_0.
   (* Henceforth the interpreter's "step" tactic will use simplifier v2.0. *)

   Note that redefinitions of PSimplifier must use "::=" not ":=" !!
 *)



(* Define tokens to denote each ltac exported by a simplifier. *)

Inductive psimpl_tactic :=
| PSIMPL_GENN | PSIMPL_GENB | PSIMPL_GENS | PSIMPL_GENU
| PSIMPL_POPULATE_VAR_IDS
| PSIMPL_N_HYP | PSIMPL_EXHYP_N | PSIMPL_EXGOAL_N
| PSIMPL_B_HYP | PSIMPL_EXHYP_B | PSIMPL_EXGOAL_B
| PSIMPL_S_HYP | PSIMPL_EXHYP_S | PSIMPL_EXGOAL_S
| PSIMPL_U_HYP | PSIMPL_EXHYP_U | PSIMPL_EXGOAL_U | PSIMPL_U_GOAL.


(* Mark all non-nested terms of type N and bool for simplification. *)

Ltac find_containing_term H v A :=
  let v' := fresh A in
  set (v':=_:A) in (value of H) at 1;
  first [ assert_succeeds (set v in (value of v') at 1)
        | let t := type of v in assert_fails (set (_:t) in (value of v') at 1) ];
  cbv delta [v] in v';
  clear v; rename v' into v.

Definition _psimpl_ (A:Type) (x:A) := x.


Module Type PSIMPL_BASE (IL: PICINAE_IL).

Ltac psimpl_mark_all_in H :=
  let P := fresh in
  set (P:=_) in (value of H);
  repeat (
    let e := fresh "e" in
    first [ set (e:=_:N) in (value of P) at 1;
            try find_containing_term P e bool;
            try find_containing_term P e IL.store
          | set (e:=_:bool) in (value of P) at 1;
            try find_containing_term P e IL.store
          | set (e:=_:IL.store) in (value of P) at 1 ];
    pattern e in (value of P);
    match type of e with
    | ?y => unify y N;        change_no_check e with (_psimpl_ N e) in (value of P)
    | ?y => unify y bool;     change_no_check e with (_psimpl_ bool e) in (value of P)
    | ?y => unify y IL.store; change_no_check e with (_psimpl_ IL.store e) in (value of P)
    end;
    let Pval := (eval cbv delta [P] in P) in
    lazymatch Pval with ?f _ =>
      let P' := fresh in
      set (P' := f) in (value of P);
      subst e P;
      rename P' into P
    end
  );
  subst P H.



(*** TOP-LEVEL SIMPLIFIER INTERFACE ***)

(* Create an initial dummy definition for PSimplifier that will later be replaced
   by one of the real simplifier definitions. *)
Ltac PSimplifier tac := fail "PSimplifier undefined. Define it with: Ltac PSimplifier ::= PSimplifier_v1_0".


(* Syntax 1: psimpl in H.
   (Simplify all terms of type N, bool, and store in hypothesis H.) *)

Ltac psimpl_vals_hyp H :=
  let t1 := fresh "sast" in
  (let t0 := fresh "sast" in
   (let t := (let Htyp := type of H in PSimplifier PSIMPL_GENU Htyp) in epose (t0:=t));
   let t0def := (eval cbv delta [t0] in t0) in let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t0def in
   clear t0; (* idtac "SASTU:" t; *) epose(t1:=t));
  PSimplifier PSIMPL_U_HYP t1 H;
  clear t1;
  PSimplifier PSIMPL_EXHYP_U H.

Ltac psimpl_hyp_ltac1 H :=
  let P := fresh in
  set (P:=_) in H;
  psimpl_mark_all_in P;
  first [ psimpl_vals_hyp H (* <-- works if H:_ is a hypothesis *)
  | (* The following works if H:=_ is a local definition: *)
    let y := fresh in let Heq := fresh in
      remember H as y eqn:Heq in *;
      subst H;
      psimpl_vals_hyp Heq;
      lazymatch type of Heq with _ = ?e => set (H:=e) in Heq end;
      try rewrite Heq in *;
      clear y Heq ];
  unfold _psimpl_ in H.


(* Syntax 2: psimpl.
   (Simplify all exps of type N, bool, and store in the goal.) *)

Ltac psimpl_vals_goal :=
  let t1 := fresh "sast" in
  (let t0 := fresh "sast" in
   (let t := (lazymatch goal with |- ?g => PSimplifier PSIMPL_GENU g end) in epose (t0:=t));
   let t0def := (eval cbv delta [t0] in t0) in let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t0def in
   clear t0; (* idtac "SASTU:" t; *) epose (t1:=t));
  PSimplifier PSIMPL_U_GOAL t1;
  clear t1;
  PSimplifier PSIMPL_EXGOAL_U.

Ltac psimpl_goal_ltac1 :=
  let P := fresh in
  set (P:=_);
  psimpl_mark_all_in P;
  psimpl_vals_goal;
  unfold _psimpl_.


(* Syntax 3: psimpl e in H.
   Syntax 4: psimpl e.
   (Simplify subexpression e (must have type N, bool, or store)
   in hypothesis H or in the goal, respectively.
   Note: e may be a pattern with wildcards (underscores).) *)

Ltac __psimpl_exp_hyp GEN HYP EXHYP x H' :=
  let t1 := fresh "sast" in
  (match type of H' with x = ?e =>
     let p := (let t := (let u := PSimplifier GEN e in type_term u) in PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t)
     in epose(t1:=p)
   end);
  PSimplifier HYP t1 H';
  clear t1;
  PSimplifier EXHYP H'.

Ltac _psimpl_exp_hyp x H' :=
  lazymatch type of x with
  | N         => __psimpl_exp_hyp PSIMPL_GENN PSIMPL_N_HYP PSIMPL_EXHYP_N x H'
  | addr      => __psimpl_exp_hyp PSIMPL_GENN PSIMPL_N_HYP PSIMPL_EXHYP_N x H'
  | memory    => __psimpl_exp_hyp PSIMPL_GENN PSIMPL_N_HYP PSIMPL_EXHYP_N x H'
  | bool      => __psimpl_exp_hyp PSIMPL_GENB PSIMPL_B_HYP PSIMPL_EXHYP_B x H'
  | IL.store  => __psimpl_exp_hyp PSIMPL_GENS PSIMPL_S_HYP PSIMPL_EXHYP_S x H'
  | IL.var->N => __psimpl_exp_hyp PSIMPL_GENS PSIMPL_S_HYP PSIMPL_EXHYP_S x H'
  | _ => psimpl_vals_hyp H'
  end.

Ltac psimpl_exp_hyp_ltac1 e H :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in H;
  _psimpl_exp_hyp x H';
  first [ rewrite H' in H (* <-- works if H:_ is a hypothesis *)
  | (* The following works if H:=_ is a local definition. *)
    subst H;
    lazymatch type of H' with _ = ?e => set (H:=e) in H' end;
    try rewrite H' in * ];
  clear x H'.

Ltac psimpl_exp_goal_ltac1 e :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in |- *;
  _psimpl_exp_hyp x H';
  rewrite H';
  clear x H'.


(* Explicit Ltac1 entry points for comparisons and compatibility. *)
Tactic Notation "psimpl_ltac1" := psimpl_goal_ltac1.
Tactic Notation "psimpl_ltac1" "in" hyp(h) := psimpl_hyp_ltac1 h.
Tactic Notation "psimpl_ltac1" uconstr(e) := psimpl_exp_goal_ltac1 uconstr:(e).
Tactic Notation "psimpl_ltac1" uconstr(e) "in" hyp(h) := psimpl_exp_hyp_ltac1 uconstr:(e) h.

(* Default implementations for third-party modules implementing this interface. *)
Ltac psimpl_goal := psimpl_goal_ltac1.
Ltac psimpl_hyp h := psimpl_hyp_ltac1 h.
Ltac psimpl_exp_goal e := psimpl_exp_goal_ltac1 e.
Ltac psimpl_exp_hyp e h := psimpl_exp_hyp_ltac1 e h.
Tactic Notation "psimpl" := psimpl_goal.
Tactic Notation "psimpl" "in" hyp(h) := psimpl_hyp h.
Tactic Notation "psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "psimpl" uconstr(e) "in" hyp(h) := psimpl_exp_hyp uconstr:(e) h.

End PSIMPL_BASE.


(* Keep Ltac2 bodies in the implementation, where Rocq checks their types.
   Check the signature without sealing: [: PSIMPL_BASE IL] would export the
   signature's Ltac1 defaults instead of the adapters defined below. *)
Module Picinae_Simplifier_Base (IL: PICINAE_IL) <: PSIMPL_BASE IL.
Include PSIMPL_BASE IL.


(* Ltac2 orchestration.  The reflective AST producer and replaceable
   PSimplifier dispatcher still exchange untyped Ltac1 terms; keep that
   boundary in Ltac1 so scoped existential variables are not elaborated early. *)
Ltac2 psimpl_vals_goal2 () :=
  let ast := Fresh.in_goal @sast in
  let ast1 := Ltac1.of_ident ast in
  ltac1:(ast |- let t0 := fresh "sast" in
    (let t := (lazymatch goal with |- ?g => PSimplifier PSIMPL_GENU g end) in epose (t0:=t));
    let def := (eval cbv delta [t0] in t0) in
    let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 def in
    clear t0; epose (ast:=t)) ast1;
  ltac1:(ast |- PSimplifier PSIMPL_U_GOAL ast) ast1;
  Std.clear [ast];
  ltac1:(PSimplifier PSIMPL_EXGOAL_U).

Ltac2 psimpl_vals_hyp2 (h : ident) :=
  let ast := Fresh.in_goal @sast in
  let ast1 := Ltac1.of_ident ast in let h1 := Ltac1.of_ident h in
  ltac1:(ast h |- let t0 := fresh "sast" in
    (let t := (let typ := type of h in PSimplifier PSIMPL_GENU typ) in epose (t0:=t));
    let def := (eval cbv delta [t0] in t0) in
    let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 def in
    clear t0; epose (ast:=t)) ast1 h1;
  ltac1:(ast h |- PSimplifier PSIMPL_U_HYP ast h) ast1 h1;
  Std.clear [ast];
  ltac1:(h |- PSimplifier PSIMPL_EXHYP_U h) h1.

(* Classic sequencing may supply several goals or none. Focus before reading
   the local context or allocating fresh identifiers. *)
Ltac2 psimpl_goal () :=
  Control.enter (fun () =>
    ltac1:(let p := fresh in set (p:=_); psimpl_mark_all_in p);
    psimpl_vals_goal2 ();
    unfold _psimpl_).

Ltac2 psimpl_hyp (h : ident) :=
  Control.enter (fun () =>
    let h1 := Ltac1.of_ident h in
    ltac1:(h |- let p := fresh in set (p:=_) in h; psimpl_mark_all_in p) h1;
    first
    [ psimpl_vals_hyp2 h
    | let y := Fresh.in_goal @y in
      let eqn := Fresh.in_goal @Heq in
      let y1 := Ltac1.of_ident y in let eq1 := Ltac1.of_ident eqn in
      ltac1:(h y heq |- remember h as y eqn:heq in *; subst h) h1 y1 eq1;
      psimpl_vals_hyp2 eqn;
      ltac1:(h heq |-
        lazymatch type of heq with _ = ?e => set (h:=e) in heq end;
        try rewrite heq in *) h1 eq1;
      Std.clear [y; eqn] ];
    unfold _psimpl_ in $h).

Ltac2 psimpl_exp_eq2 (gen : constr) (hyp : constr) (exhyp : constr)
    (x : ident) (eqn : ident) :=
  let ast := Fresh.in_goal @sast in
  let ast1 := Ltac1.of_ident ast in
  let x1 := Ltac1.of_ident x in let eq1 := Ltac1.of_ident eqn in
  let gen1 := Ltac1.of_constr gen in
  ltac1:(gen x heq ast |- match type of heq with x = ?e =>
    let p := (let t := (let u := PSimplifier gen e in type_term u) in
      PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t) in epose (ast:=p)
    end) gen1 x1 eq1 ast1;
  let hyp1 := Ltac1.of_constr hyp in
  ltac1:(hyp ast heq |- PSimplifier hyp ast heq) hyp1 ast1 eq1;
  Std.clear [ast];
  let exhyp1 := Ltac1.of_constr exhyp in
  ltac1:(exhyp heq |- PSimplifier exhyp heq) exhyp1 eq1.

Ltac2 psimpl_exp_dispatch2 (x : ident) (eqn : ident) :=
  lazy_match! Constr.type (Control.hyp x) with
  | N => psimpl_exp_eq2 constr:(PSIMPL_GENN) constr:(PSIMPL_N_HYP) constr:(PSIMPL_EXHYP_N) x eqn
  | addr => psimpl_exp_eq2 constr:(PSIMPL_GENN) constr:(PSIMPL_N_HYP) constr:(PSIMPL_EXHYP_N) x eqn
  | memory => psimpl_exp_eq2 constr:(PSIMPL_GENN) constr:(PSIMPL_N_HYP) constr:(PSIMPL_EXHYP_N) x eqn
  | bool => psimpl_exp_eq2 constr:(PSIMPL_GENB) constr:(PSIMPL_B_HYP) constr:(PSIMPL_EXHYP_B) x eqn
  | IL.store => psimpl_exp_eq2 constr:(PSIMPL_GENS) constr:(PSIMPL_S_HYP) constr:(PSIMPL_EXHYP_S) x eqn
  | IL.var -> N => psimpl_exp_eq2 constr:(PSIMPL_GENS) constr:(PSIMPL_S_HYP) constr:(PSIMPL_EXHYP_S) x eqn
  | _ => psimpl_vals_hyp2 eqn
  end.

(* Expression patterns use Ltac1 remember, which accepts uconstr wildcards
   without elaborating them before the occurrence has been selected. *)
Ltac2 psimpl_exp_hyp (e : Ltac1.t) (h : ident) :=
  Control.enter (fun () =>
    let x := Fresh.in_goal @x in
    let eqn := Fresh.in_goal @Heq in
    let x1 := Ltac1.of_ident x in let eq1 := Ltac1.of_ident eqn in
    let h1 := Ltac1.of_ident h in
    ltac1:(e h x heq |- remember e as x eqn:heq in h) e h1 x1 eq1;
    psimpl_exp_dispatch2 x eqn;
    first
    [ ltac1:(heq h |- rewrite heq in h) eq1 h1
    | ltac1:(heq h |- subst h;
        lazymatch type of heq with _ = ?e => set (h:=e) in heq end;
        try rewrite heq in *) eq1 h1 ];
    Std.clear [x; eqn]).

Ltac2 psimpl_exp_goal (e : Ltac1.t) :=
  Control.enter (fun () =>
    let x := Fresh.in_goal @x in
    let eqn := Fresh.in_goal @Heq in
    let x1 := Ltac1.of_ident x in let eq1 := Ltac1.of_ident eqn in
    ltac1:(e x heq |- remember e as x eqn:heq in |- *) e x1 eq1;
    psimpl_exp_dispatch2 x eqn;
    ltac1:(heq |- rewrite heq) eq1;
    Std.clear [x; eqn]).

(* Classic-mode adapters preserve existing scripts and architecture aliases. *)
Ltac psimpl_goal ::= ltac2:(psimpl_goal ()).
Ltac psimpl_hyp h ::=
  let f := ltac2:(h |- psimpl_hyp (picinae_hyp_ident h)) in f h.
Ltac psimpl_exp_goal e ::= let f := ltac2:(e |- psimpl_exp_goal e) in f e.
Ltac psimpl_exp_hyp e h ::=
  let f := ltac2:(e h |- psimpl_exp_hyp e (picinae_hyp_ident h)) in f e h.
Tactic Notation "psimpl" := psimpl_goal.
Tactic Notation "psimpl" "in" hyp(h) := psimpl_hyp h.
Tactic Notation "psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "psimpl" uconstr(e) "in" hyp(h) := psimpl_exp_hyp uconstr:(e) h.

End Picinae_Simplifier_Base.
