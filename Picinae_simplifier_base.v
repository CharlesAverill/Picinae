(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
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

Require Import NArith.
Require Import Picinae_core.
Require Import Picinae_finterp.

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

Ltac psimpl_hyp H :=
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

Tactic Notation "psimpl" "in" hyp(H) := psimpl_hyp H.


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

Ltac psimpl_goal :=
  let P := fresh in
  set (P:=_);
  psimpl_mark_all_in P;
  psimpl_vals_goal;
  unfold _psimpl_.

Tactic Notation "psimpl" := psimpl_goal.


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

Ltac psimpl_exp_hyp e H :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in H;
  _psimpl_exp_hyp x H';
  first [ rewrite H' in H (* <-- works if H:_ is a hypothesis *)
  | (* The following works if H:=_ is a local definition. *)
    subst H;
    lazymatch type of H' with _ = ?e => set (H:=e) in H' end;
    try rewrite H' in * ];
  clear x H'.

Ltac psimpl_exp_goal e :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in |- *;
  _psimpl_exp_hyp x H';
  rewrite H';
  clear x H'.

Tactic Notation "psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).

End PSIMPL_BASE.


Module Picinae_Simplifier_Base (IL: PICINAE_IL) : PSIMPL_BASE IL.
  Include PSIMPL_BASE IL.
End Picinae_Simplifier_Base.
