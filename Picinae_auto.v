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
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Automation Extensions Module:                       MMMMMMMMMMMMMMMMM^NZMMN+Z
   * rewriting store infoormation.                      MMMMMMMMMMMMMMM/.$MZM8O+
   * lia pre-processing configuration                    MMMMMMMMMMMMMM7..$MNDM+
                                                          MMDMMMMMMMMMZ7..$DM$77
                                                           MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
   To compile this module, first load and compile:           MMMMMMMMMM$.$MOMO=7
   * Picinae_core                                             MDMMMMMMMO.7MDM7M+
   * Picinae_theory                                            ZMMMMMMMM.$MM8$MN
   * Picinae_statics                                           $ZMMMMMMZ..MMMOMZ
   Then compile this module with menu option                    ?MMMMMM7..MNN7$M
   Compile->Compile_buffer.                                      ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Import NArith.
Require Import Picinae_theory.
Require Import Picinae_statics.
Require Export Lia ZifyN ZifyBool.
Open Scope N.

Module PicinaeAuto (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL) (SIL: PICINAE_STATICS IL TIL).
Import SIL.

(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat lazymatch goal with
  | [ H: ?s ?v = _, MDL: models ?typs ?s |- _] =>
      let Hyp := fresh "SBound" in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      (** Keep limit if bitwidth is small; if it is large lia will hang. *)
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end;
      try rewrite H in *; clear H; try clear s MDL
  end.

Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *.

End PicinaeAuto.
