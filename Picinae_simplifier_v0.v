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
                                                         MMMMMMMMMMMMMM7..$MNDM+
   To compile this module, first compile:                 MMDMMMMMMMMMZ7..$DM$77
   * Picinae_core                                          MMMMMMM+MMMZ7..7ZM~++
   * Picinae_theory                                         MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_simplifier_base                                  MDMMMMMMMO.7MDM7M+
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

Require Import Picinae_core.
Require Import Picinae_theory.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Export Picinae_simplifier_base.
Require Import BinNums.

(* Version 0 of the simplifier does nothing.  Activating this version therefore
   allows the user to turn off all auto-simplification. *)

Module Type PICINAE_SIMPLIFIER_V0
  (IL: PICINAE_IL)
  (TIL: PICINAE_THEORY IL)
  (SIL: PICINAE_STATICS IL TIL)
  (FIL: PICINAE_FINTERP IL TIL SIL).

Import IL.
Import TIL.
Import SIL.
Import FIL.

Local Ltac dummy_gen e := uconstr:(tt).
Local Ltac dummy_populate id t := uconstr:(tt).
Local Ltac idtac1 x := idtac.
Local Ltac idtac2 x y := idtac.

Ltac PSimplifier tac :=
  lazymatch tac with
  | PSIMPL_GENN => dummy_gen
  | PSIMPL_GENB => dummy_gen
  | PSIMPL_GENS => dummy_gen
  | PSIMPL_GENU => dummy_gen
  | PSIMPL_POPULATE_VAR_IDS => dummy_populate
  | PSIMPL_N_HYP => idtac2
  | PSIMPL_B_HYP => idtac2
  | PSIMPL_S_HYP => idtac2
  | PSIMPL_U_HYP => idtac2
  | PSIMPL_U_GOAL => idtac1
  | PSIMPL_EXHYP_N => idtac1
  | PSIMPL_EXGOAL_N => idtac
  | PSIMPL_EXHYP_B => idtac1
  | PSIMPL_EXGOAL_B => idtac
  | PSIMPL_EXHYP_S => idtac1
  | PSIMPL_EXGOAL_S => idtac
  | PSIMPL_EXHYP_U => idtac1
  | PSIMPL_EXGOAL_U => idtac
  end.

End PICINAE_SIMPLIFIER_V0.



Module Picinae_Simplifier_v0
  (IL: PICINAE_IL)
  (TIL: PICINAE_THEORY IL)
  (SIL: PICINAE_STATICS IL TIL)
  (FIL: PICINAE_FINTERP IL TIL SIL)
  : PICINAE_SIMPLIFIER_V0 IL TIL SIL FIL.

Import IL.
Import TIL.
Import SIL.
Import FIL.

End Picinae_Simplifier_v0.
