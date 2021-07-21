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



(* Create an initial dummy definition for PSimplifier that will later be replaced
   by one of the real simplifier definitions. *)

Ltac PSimplifier tac := fail "PSimplifier undefined. Define it with: Ltac PSimplifier ::= PSimplifier_v1_0".


(* Define tokens to denote each ltac exported by a simplifier. *)

Inductive psimpl_tactic :=
| PSIMPL_INIT
| PSIMPL_GENN | PSIMPL_GENV | PSIMPL_GENU
| PSIMPL_POPULATE_VAR_IDS
| PSIMPL_N_HYP | PSIMPL_V_HYP | PSIMPL_V_GOAL | PSIMPL_U_HYP | PSIMPL_U_GOAL
| PSIMPL_EXHYP_N | PSIMPL_EXGOAL_N | PSIMPL_EXHYP_V | PSIMPL_EXGOAL_V | PSIMPL_EXHYP_U | PSIMPL_EXGOAL_U.


(*** TOP-LEVEL SIMPLIFIER INTERFACE ***)

(* Syntax: psimpl e in H.
   Description: Simplify numeric subexpression e (must have type N) in hypothesis H.
   Note: e may be a pattern with wildcards (underscores). *)

Tactic Notation "psimpl" uconstr(e) "in" hyp(H) :=
  PSimplifier PSIMPL_INIT;
  let x := fresh "n" in let H' := fresh "Heq" x in remember (e:N) as x eqn:H' in H;
  let t1 := fresh "sast" in
  (match type of H' with x = ?n =>
     let p := (let t := (let u := PSimplifier PSIMPL_GENN n in type_term u) in PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t)
     in epose(t1:=p)
   end);
  PSimplifier PSIMPL_N_HYP t1 H';
  clear t1;
  PSimplifier PSIMPL_EXHYP_N H';
  rewrite H' in H;
  clear x H'.

(* Syntax: psimpl e.
   Description: Simplify numeric subexpression e (must have type N) in the goal.
   Note: e may be a pattern with wildcards (underscores). *)

Tactic Notation "psimpl" uconstr(e) :=
  PSimplifier PSIMPL_INIT;
  let x := fresh "n" in let H' := fresh "Heq" x in remember (e:N) as x eqn:H' in |- *;
  let t1 := fresh "sast" in
  (match type of H' with x = ?n =>
     let p := (let t := (let u := PSimplifier PSIMPL_GENN n in type_term u) in PSimplifier PSIMPL_POPULATE_VAR_IDS N0 t)
     in epose(t1:=p)
   end);
  PSimplifier PSIMPL_N_HYP t1 H';
  clear t1;
  PSimplifier PSIMPL_EXHYP_N H';
  rewrite H';
  clear x H'.

(* Syntax: psimpl in H.
   Description: Simplify all Picinae IL values (VaN/VaM) in hypothesis H. *)

Tactic Notation "psimpl" "in" hyp(H) :=
  PSimplifier PSIMPL_INIT;
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

(* Syntax: psimpl.
   Description: Simplify all Picinae IL values (VaN/VaM) in the goal. *)

Tactic Notation "psimpl" :=
  PSimplifier PSIMPL_INIT;
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
