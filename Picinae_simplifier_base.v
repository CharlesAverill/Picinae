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

Require Import BinNums.
Require Import Picinae_core.

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



(*** TOP-LEVEL SIMPLIFIER INTERFACE ***)

Module Picinae_Simplifier_Base.

(* Create an initial dummy definition for PSimplifier that will later be replaced
   by one of the real simplifier definitions. *)
Ltac PSimplifier tac := fail "PSimplifier undefined. Define it with: Ltac PSimplifier ::= PSimplifier_v1_0".


(* Syntax: psimpl in H.
   Description: Simplify all Picinae IL values (VaN/VaM) in hypothesis H. *)

Ltac psimpl_hyp H :=
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

Tactic Notation "psimpl" "in" hyp(H) := psimpl_hyp H.


(* Syntax: psimpl.
   Description: Simplify all Picinae IL values (VaN/VaM) in the goal. *)

Ltac psimpl_goal :=
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

Tactic Notation "psimpl" := psimpl_goal.


Ltac _psimpl_hyp GEN HYP EXHYP x H' :=
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
  | N        => _psimpl_hyp PSIMPL_GENN PSIMPL_N_HYP PSIMPL_EXHYP_N x H'
  | bool     => _psimpl_hyp PSIMPL_GENB PSIMPL_B_HYP PSIMPL_EXHYP_B x H'
  | addr->N  => _psimpl_hyp PSIMPL_GENM PSIMPL_M_HYP PSIMPL_EXHYP_M x H'
  | _ => psimpl_hyp H'
  end.


(* Syntax: psimpl e in H.
   Description: Simplify subexpression e (must have type N, bool, mem, value, or store)
   in hypothesis H.  Note: e may be a pattern with wildcards (underscores). *)

Ltac psimpl_exp_hyp e H :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in H;
  _psimpl_exp_hyp x H';
  rewrite H' in H;
  clear x H'.

Tactic Notation "psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.


(* Syntax: psimpl e.
   Description: Simplify subexpression e (must have type N, bool, mem, value, or store)
   in the goal.  Note: e may be a pattern with wildcards (underscores). *)

Ltac psimpl_exp_goal e :=
  let x := fresh in let H' := fresh in
  remember e as x eqn:H' in |- *;
  _psimpl_exp_hyp x H';
  rewrite H';
  clear x H'.

Tactic Notation "psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).

End Picinae_Simplifier_Base.
