(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2022 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
     module (e.g., Picinae_simplifier_v1_0.v).              MMMMMMMMMMM7..ZNOOMZ
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
| PSIMPL_GENN | PSIMPL_GENM | PSIMPL_GENB | PSIMPL_GENS | PSIMPL_GENV | PSIMPL_GENU
| PSIMPL_POPULATE_VAR_IDS
| PSIMPL_N_HYP | PSIMPL_EXHYP_N | PSIMPL_EXGOAL_N
| PSIMPL_B_HYP | PSIMPL_EXHYP_B | PSIMPL_EXGOAL_B
| PSIMPL_M_HYP | PSIMPL_EXHYP_M | PSIMPL_EXGOAL_M
| PSIMPL_S_HYP | PSIMPL_EXHYP_S | PSIMPL_EXGOAL_S
| PSIMPL_V_HYP | PSIMPL_EXHYP_V | PSIMPL_EXGOAL_V | PSIMPL_V_GOAL
| PSIMPL_U_HYP | PSIMPL_EXHYP_U | PSIMPL_EXGOAL_U | PSIMPL_U_GOAL.


(* Mark all non-nested terms of type N, bool, and addr->N for simplification. *)

Definition _psiN u := match u with VaN n _ => n | _ => N0 end.
Definition _psiB (b:bool) := b.
Definition _psiM u := match u with VaM m _ => m | _ => fun _ => 0 end.

Ltac find_containing_term H v A :=
  let v' := fresh A in
  set (v':=_:A) in (value of H) at 1; first
  [ let test := fresh in
    set (test:=v) in (value of v') at 1;
    subst test v;
    rename v' into v
  | subst v' ].

Ltac psimpl_mark_all_in H :=
  let P := fresh in
  set (P:=_) in (value of H);
  repeat (
    let u := fresh "u" in
    set (u:=_:value) in (value of P) at 1;
    fold u in (value of P);
    pattern u in (value of P);
    let Pval := (eval cbv delta [P] in P) in
    lazymatch Pval with ?f u =>
      let P' := fresh in
      set (P' := f) in (value of P);
      subst u P; rename P' into P
    end
  );
  repeat (
    let e := fresh "e" in
    first [ set (e:=_:N) in (value of P) at 1;
            try find_containing_term P e bool;
            try find_containing_term P e (addr->N)
          | set (e:=_:bool) in (value of P) at 1;
            try find_containing_term P e (addr->N)
          | set (e:=_:addr->N) in (value of P) at 1 ];
    pattern e in (value of P);
    lazymatch type of e with
    | N => change e with (_psiN (VaN e 1)) in (value of P)
    | bool => change e with (_psiB e) in (value of P)
    | N->addr => change e with (_psiM (VaM e 1)) in (value of P)
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

Module Picinae_Simplifier_Base.

(* Create an initial dummy definition for PSimplifier that will later be replaced
   by one of the real simplifier definitions. *)
Ltac PSimplifier tac := fail "PSimplifier undefined. Define it with: Ltac PSimplifier ::= PSimplifier_v1_0".


(* Syntax 1: psimpl in H.      (* simply all terms of type N, bool, and addr->N in hypothesis H *)
   Syntax 2: psimpl_vals in H. (* only simplify the terms within IL values (much faster!) *) *)

Ltac psimpl_vals_hyp H :=
  let t1 := fresh "sast" in
  (let t := (let Htyp := type of H in PSimplifier PSIMPL_GENV Htyp) in
   (* idtac "SASTV:" t; *) epose (t1:=t));
  PSimplifier PSIMPL_V_HYP t1 H;
  clear t1;
  PSimplifier PSIMPL_EXHYP_V H;
  (let t0 := fresh "sast" in
   (let t := (let Htyp := type of H in PSimplifier PSIMPL_GENU Htyp) in epose (t0:=t));
   let t0def := (eval cbv delta [t0] in t0) in let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t0def in
   clear t0; (* idtac "SASTU:" t; *) epose(t1:=t));
  PSimplifier PSIMPL_U_HYP t1 H;
  clear t1;
  PSimplifier PSIMPL_EXHYP_U H.

Ltac psimpl_all_hyp H :=
  let P := fresh in
  set (P:=_) in H;
  psimpl_mark_all_in P;
  psimpl_vals_hyp H;
  unfold _psiN,_psiB,_psiM in H.

Tactic Notation "psimpl_vals" "in" hyp(H) := psimpl_vals_hyp H.
Tactic Notation "psimpl" "in" hyp(H) := psimpl_all_hyp H.


(* Syntax 1: psimpl.      (* Simplify all exps of type N, bool, and addr->N in the goal. *)
   Syntax 2: psimpl_vals. (* Only simplify the terms in IL values (much faster!) *) *)

Ltac psimpl_vals_goal :=
  let t1 := fresh "sast" in
  (let t := (lazymatch goal with |- ?g => PSimplifier PSIMPL_GENV g end) in
   (* idtac "SASTV:" t; *) epose (t1:=t));
  PSimplifier PSIMPL_V_GOAL t1;
  clear t1;
  PSimplifier PSIMPL_EXGOAL_V;
  (let t0 := fresh "sast" in
   (let t := (lazymatch goal with |- ?g => PSimplifier PSIMPL_GENU g end) in epose (t0:=t));
   let t0def := (eval cbv delta [t0] in t0) in let t := PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t0def in
   clear t0; (* idtac "SASTU:" t; *) epose (t1:=t));
  PSimplifier PSIMPL_U_GOAL t1;
  clear t1;
  PSimplifier PSIMPL_EXGOAL_U.

Ltac psimpl_all_goal :=
  let P := fresh in
  set (P:=_);
  psimpl_mark_all_in P;
  psimpl_vals_goal;
  unfold _psiN,_psiB,_psiM.

Tactic Notation "psimpl_vals" := psimpl_vals_goal.
Tactic Notation "psimpl" := psimpl_all_goal.


(* Syntax 1: psimpl e in H.
   Syntax 2: psimpl e.
   Description: Simplify subexpression e (must have type N, bool, mem, value, or store)
   in hypothesis H or in the goal.  Note: e may be a pattern with wildcards (underscores). *)

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
  | N        => __psimpl_exp_hyp PSIMPL_GENN PSIMPL_N_HYP PSIMPL_EXHYP_N x H'
  | bool     => __psimpl_exp_hyp PSIMPL_GENB PSIMPL_B_HYP PSIMPL_EXHYP_B x H'
  | addr->N  => __psimpl_exp_hyp PSIMPL_GENM PSIMPL_M_HYP PSIMPL_EXHYP_M x H'
  | _ => psimpl_vals_hyp H'
  end.

Ltac psimpl_exp_hyp e H :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in H;
  _psimpl_exp_hyp x H';
  rewrite H' in H;
  clear x H'.

Ltac psimpl_exp_goal e :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in |- *;
  _psimpl_exp_hyp x H';
  rewrite H';
  clear x H'.

Tactic Notation "psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).

End Picinae_Simplifier_Base.
