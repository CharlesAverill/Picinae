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
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Automation Extensions Module:                       MMMMMMMMMMMMMMMMM^NZMMN+Z
   * rewriting store infoormation.                      MMMMMMMMMMMMMMM/.$MZM8O+
   * lia pre-processing configuration                    MMMMMMMMMMMMMM7..$MNDM+
   * arithmetic and boolean simplifiers                   MMDMMMMMMMMMZ7..$DM$77
   * bit-injection solver/reducer                          MMMMMMM+MMMZ7..7ZM~++
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

From Stdlib Require Import NArith.
Require Import Picinae_theory.
Require Import Picinae_statics.
From Stdlib Require Export Lia ZifyN ZifyBool.
From Ltac2 Require Import Ltac2 Printf Std.
Set Default Proof Mode "Classic".
Open Scope bool.

(*  The PicinaeAuto module provides some useful tactics for simplifying typical
    Picinae goals.  To use it you need to add it to the module instantiation list
    in your architecture's specification file.  E.g.,
    <<
      Module Auto_arm8 := PicinaeAuto IL_arm8 Theory_arm8 Statics_arm8.
      Export Auto_arm8.
    >>

    The simplifiers are designed to make safe and simple rewrites.  The available
    simplifiers are:

      * elimstore---elimstore "eliminates" hypotheses and values of the form `s v = _`
          by substituting them or introducing a variable where possible and
          introducing a bound on their value using the `models _ s` hypothesis.
          Ideally, it will clear all store variables and models hypotheses, leaving
          only N's in its wake.

      * asimpl---asimpl simplifies arithmetic expressions over N using reducing
          rewrites.  It cannot handle complex reasoning.  For example, it cannot
          simplify `a+b+c-a` to `b+c`, because the two `a` operands are too far
          apart.  For this complicated simplification `psimpl` works better.
          However, psimpl will not always simplify goals that `asimpl` simplfies,
          and it is typically slower.

      * bsimpl---bsimpl simplifies boolean expressions, as well as boolean
          comparisons over N.  For the comparisons, it either replaces them with
          `false` or `true`, or it destructs them and adds the equation to
          the context.

          Variations:
            `bsimpl in H.` runs bsimpl on hypothesis H.
            `simple_bsimpl.` runs bsimpl without `lia`/`smt`.

      * csimpl---csimpl rewrites boolean-valued comparison equalities to their
          propositional form.  E.g., `H: x =? y = true` becomes `H: x = y`
          and `P: x <=? y = false` becomes `P: x > y`.

      * specsimpl---specsimpl simplifies N.testbit expressions.  It exclusively
          uses rewrites that do not introduce hypotheses.  Instead its rewrites
          may introduce comparisons over N.

          Variation: `simple_specsimpl` runs specsimpl without `lia`/`smt`.

      * bitify---bitify tries to turn all possible arithmetic expressions to bit
          operations.  Right now only supports turning multiplication by constants
          into left shift.

      * algify---algify inverses bitify, turning bitwise operations into algebraic
          operations (multiplication, division).  This is important as lia and smt
          only understand the multiplication and division versions, leaving them
          as left and right bit-shifts may prevent lia/smt from solving the goal.

          N.B.  Rule of thumb: bitify before doing bitwise operation reasoning
          (e.g., solve bits inj); algify before using lia or smt.

    PicinaeAuto provides a new solver and configures the Rocq-native solver lia.

      * lia---lia is configured by exporting ZifyN, ZifyBool, and by adding
          the `elimstore` simplifier to the zify_pre_hook and unfolding msub.
          In conjunction, these changes make solving some arithmetic invariants
          trivial with just `lia.`.  ZifyN and ZifyB empower lia to reason about
          N.pow, N.mod and boolean N comparisons.

      * solve bits inj---The `solve bits inj` solver, written with spaces,
          starts, reduces, and attempts to solve an N equality goal using the
          bit-injection proof strategy.  That is, it uses specsimpl, asimpl,
          bsimpl, and an arithmetic solver to try to prove that each bit of the
          two numbers must be equal.  If it gets hung up you can add a timeout
          or manually use the sbi0* tactics that implement the simplification
          loop.

          Variation: `solve bits inj X.` runs the solver with a timeout of X
            seconds for each call to `lia`/`smt`.  By default X is zero, meaning
            no timeout.

          N.B.  Install `coq-itauto` and require the file `Cdcl.NOlia` to use
          the `smt` arithmetic solver.  This is a more powerful version of `lia`,
          which the solver will fall back to if `smt` is not available.
          I.e., run `opam install coq-itauto` in your terminal to install the
          `coq-itauto` package, then add the line `Require Cdcl.NOlia.` or
          `Require Import Cdcl.NOlia.` in your .v file.

          N.B.  You will also need to `Require Import ZifyN ZifyBool.` in the same
          file you require `Cdcl.NOlia` to empower `smt` with boolean-, modulo-,
          and exponentiation-reasoning.  The exports from this file are not enough.
 *)

Module PicinaeAuto (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL) (SIL: PICINAE_STATICS IL TIL).
Import SIL.

Ltac2 lia_or_smt0 () :=
    (* check arbitrary reference from same module because Ltac1.ref error is not catchable *)
    match Env.get [@Cdcl;@NOlia;@ZarithThy] with
    | Some _ => Ltac1.run (Ltac1.ref [@Cdcl;@NOlia;@smt])
    | None => Ltac1.run (Ltac1.ref [@Stdlib;@micromega;@Lia;@lia])
    end.
Tactic Notation "lia_or_smt" := ltac2:(lia_or_smt0 ()).

(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat lazymatch goal with
  (* Eliminate registers we have an expression for. *)
  | [ H: ?s ?v = _, MDL: models ?typs ?s |- _] =>
      let Hyp := fresh "SBound" in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      (** Keep limit if bitwidth is small; if it is large lia will hang. *)
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end;
      try rewrite H in *; clear H; try clear s
  (* Eliminate register we use in hypotheses but do not have an expression for. *)
  | [ MDL: models ?typs ?s, H:context[?s ?v] |- _] =>
      let Hyp := fresh "SBound" in
      let vv := fresh "v" v in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      remember (s v) as vv eqn:Heq;
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end; clear Heq; try clear s
  (* Eliminate register we use in the goal but do not have an expression for. *)
  | [ MDL: models ?typs ?s |- context[?s ?v]] =>
      let Hyp := fresh "SBound" in
      let vv := fresh "v" v in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      remember (s v) as vv eqn:Heq;
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end; clear Heq; try clear s
  end;
  try match goal with
  | MDL: models _ _ |- _ => clear MDL
  end.

Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *.

(* Brief section with specialized simple lemmas and the `solve simple bound` solver. *)
Corollary mp2_bound_trans_lt:
  forall a w w', a < 2^w -> w < w' -> a < 2^w'.
Proof. intros. apply N.lt_trans with (m:=2^w); (assumption || apply N.pow_lt_mono_r; lia). Qed.
Corollary mp2_bound_trans_le:
  forall a w w', a < 2^w -> w <= w' -> a < 2^w'.
Proof. intros. apply N.lt_le_trans with (m:=2^w); (assumption || apply N.pow_le_mono_r; lia). Qed.

Tactic Notation "solve" "simple" "bound" :=
  (eapply mp2_bound_trans_lt + eapply mp2_bound_trans_le); try eassumption; lia.

Lemma Nleb_add_l: forall a b, a <=? b+a = true. Proof. lia. Qed.
Lemma Nleb_add_r: forall a b, a <=? a+b = true. Proof. lia. Qed.
Lemma Nltb_add_l: forall a b n, n +a <? n+b = (a<? b). Proof. lia. Qed.
Lemma Nltb_add_r: forall a b n, a +n <? b+n = (a<? b). Proof. lia. Qed.

Lemma Nred_add_cancel_l: forall n a b, a=b -> n+a = n+b. Proof. lia. Qed.
Lemma Nred_add_cancel_r: forall n a b, a=b -> a+n = b+n. Proof. lia. Qed.
Lemma Nred_add_cancel_lr: forall n a b, a=b -> n+a = b+n. Proof. lia. Qed.
Lemma Nred_add_cancel_rl: forall n a b, a=b -> a+n = n+b. Proof. lia. Qed.

(* We include some corollaries of theorems with the constant 2^w.  Often for
   low values we will not have the exponent, and it is simpler to add some
   corollaries than try to figure out which values to rewrite and when. *)
Lemma Ntestbit_1:
  forall i, N.testbit 1 i = (0 =? i).
Proof.
  intros. replace 1 with (2^0) by reflexivity.
  rewrite N.pow2_bits_eqb. reflexivity.
Qed.

Theorem Ntestbit_bound_cancel:
  forall a w i, a < 2^w -> N.testbit a i && (i<?w) = N.testbit a i.
Proof.
  intros. destruct (_<?_) eqn:Eqn. rewrite Bool.andb_true_r; reflexivity.
  rewrite bits_above_pow2. reflexivity.
  solve simple bound.
Qed.

Corollary Nmod_pow2_bits_2:
  forall a m, N.testbit (a mod 2) m = (m <? 1) && (N.testbit a m).
Proof. intros. replace (a mod 2) with (a mod 2^1) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_4:
  forall a m, N.testbit (a mod 4) m = (m <? 2) && (N.testbit a m).
Proof. intros. replace (a mod 4) with (a mod 2^2) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_8:
  forall a m, N.testbit (a mod 8) m = (m <? 3) && (N.testbit a m).
Proof. intros. replace (a mod 8) with (a mod 2^3) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_16:
  forall a m, N.testbit (a mod 16) m = (m <? 4) && (N.testbit a m).
Proof. intros. replace (a mod 16) with (a mod 2^4) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_32:
  forall a m, N.testbit (a mod 32) m = (m <? 5) && (N.testbit a m).
Proof. intros. replace (a mod 32) with (a mod 2^5) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_64:
  forall a m, N.testbit (a mod 64) m = (m <? 6) && (N.testbit a m).
Proof. intros. replace (a mod 64) with (a mod 2^6) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_128:
  forall a m, N.testbit (a mod 128) m = (m <? 7) && (N.testbit a m).
Proof. intros. replace (a mod 128) with (a mod 2^7) by reflexivity. apply Nmod_pow2_bits. Qed.
Corollary Nmod_pow2_bits_256:
  forall a m, N.testbit (a mod 256) m = (m <? 8) && (N.testbit a m).
Proof. intros. replace (a mod 256) with (a mod 2^8) by reflexivity. apply Nmod_pow2_bits. Qed.

Corollary mp2_shiftl_2_r:
  forall a, a*2 = a<<1.
Proof. symmetry; replace 2 with (2^1);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_4_r:
  forall a, a*4 = a<<2.
Proof. symmetry; replace 4 with (2^2);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_8_r:
  forall a, a*8 = a<<3.
Proof. symmetry; replace 8 with (2^3);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_16_r:
  forall a, a*16 = a<<4.
Proof. symmetry; replace 16 with (2^4);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_32_r:
  forall a, a*32 = a<<5.
Proof. symmetry; replace 32 with (2^5);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_64_r:
  forall a, a*64 = a<<6.
Proof. symmetry; replace 64 with (2^6);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_2_l:
  forall a, 2*a = a<<1.
Proof. symmetry; rewrite N.mul_comm; replace 2 with (2^1);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_4_l:
  forall a, 4*a = a<<2.
Proof. symmetry; rewrite N.mul_comm; replace 4 with (2^2);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_8_l:
  forall a, 8*a = a<<3.
Proof. symmetry; rewrite N.mul_comm; replace 8 with (2^3);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_16_l:
  forall a, 16*a = a<<4.
Proof. symmetry; rewrite N.mul_comm; replace 16 with (2^4);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_32_l:
  forall a, 32*a = a<<5.
Proof. symmetry; rewrite N.mul_comm; replace 32 with (2^5);[apply N.shiftl_mul_pow2|];lia. Qed.
Corollary mp2_shiftl_64_l:
  forall a, 64*a = a<<6.
Proof. symmetry; rewrite N.mul_comm; replace 64 with (2^6);[apply N.shiftl_mul_pow2|];lia. Qed.

Corollary mp2_shiftr_2:
  forall a, a/2 = a>>1.
Proof. symmetry; replace 2 with (2^1);[apply N.shiftr_div_pow2|];lia. Qed.
Corollary mp2_shiftr_4:
  forall a, a/4 = a>>2.
Proof. symmetry; replace 4 with (2^2);[apply N.shiftr_div_pow2|];lia. Qed.
Corollary mp2_shiftr_8:
  forall a, a/8 = a>>3.
Proof. symmetry; replace 8 with (2^3);[apply N.shiftr_div_pow2|];lia. Qed.
Corollary mp2_shiftr_16:
  forall a, a/16 = a>>4.
Proof. symmetry; replace 16 with (2^4);[apply N.shiftr_div_pow2|];lia. Qed.
Corollary mp2_shiftr_32:
  forall a, a/32 = a>>5.
Proof. symmetry; replace 32 with (2^5);[apply N.shiftr_div_pow2|];lia. Qed.
Corollary mp2_shiftr_64:
  forall a, a/64 = a>>6.
Proof. symmetry; replace 64 with (2^6);[apply N.shiftr_div_pow2|];lia. Qed.

Corollary mp2_mod_2:
  forall a, a mod 2 = a mod 2^1.
Proof. lia. Qed.
Corollary mp2_mod_4:
  forall a, a mod 4 = a mod 2^2.
Proof. lia. Qed.
Corollary mp2_mod_8:
  forall a, a mod 8 = a mod 2^3.
Proof. lia. Qed.
Corollary mp2_mod_16:
  forall a, a mod 16 = a mod 2^4.
Proof. lia. Qed.
Corollary mp2_mod_32:
  forall a, a mod 32 = a mod 2^5.
Proof. lia. Qed.
Corollary mp2_mod_64:
  forall a, a mod 64 = a mod 2^6.
Proof. lia. Qed.
Corollary mp2_mod_128:
  forall a, a mod 128 = a mod 2^7.
Proof. lia. Qed.
Corollary mp2_mod_256:
  forall a, a mod 256 = a mod 2^8.
Proof. lia. Qed.

Ltac bitify :=
  rewrite ?mp2_shiftl_2_r, ?mp2_shiftl_4_r, ?mp2_shiftl_8_r,
          ?mp2_shiftl_16_r, ?mp2_shiftl_32_r, ?mp2_shiftl_64_r,
          ?mp2_shiftl_2_l, ?mp2_shiftl_4_l, ?mp2_shiftl_8_l,
          ?mp2_shiftl_16_l, ?mp2_shiftl_32_l, ?mp2_shiftl_64_l,
          ?mp2_shiftr_2, ?mp2_shiftr_4, ?mp2_shiftr_8,
          ?mp2_shiftr_16, ?mp2_shiftr_32, ?mp2_shiftr_64,
          ?mp2_mod_2, ?mp2_mod_4, ?mp2_mod_8, ?mp2_mod_16,
          ?mp2_mod_32, ?mp2_mod_64, ?mp2_mod_128, ?mp2_mod_256
  in * |- *;
  repeat match goal with
  | [H: _ < 2 |- _] => replace 2 with (2^1) in H by reflexivity
  | [H: _ < 4 |- _] => replace 4 with (2^2) in H by reflexivity
  | [H: _ < 8 |- _] => replace 8 with (2^3) in H by reflexivity
  | [H: _ < 16 |- _] => replace 16 with (2^4) in H by reflexivity
  | [H: _ < 32 |- _] => replace 32 with (2^5) in H by reflexivity
  | [H: _ < 64 |- _] => replace 64 with (2^6) in H by reflexivity
  | [H: _ < 128 |- _] => replace 128 with (2^7) in H by reflexivity
  | [H: _ < 256 |- _] => replace 256 with (2^8) in H by reflexivity
  | [H: _ <= 2 |- _] => replace 2 with (2^1) in H by reflexivity
  | [H: _ <= 4 |- _] => replace 4 with (2^2) in H by reflexivity
  | [H: _ <= 8 |- _] => replace 8 with (2^3) in H by reflexivity
  | [H: _ <= 16 |- _] => replace 16 with (2^4) in H by reflexivity
  | [H: _ <= 32 |- _] => replace 32 with (2^5) in H by reflexivity
  | [H: _ <= 64 |- _] => replace 64 with (2^6) in H by reflexivity
  | [H: _ <= 128 |- _] => replace 128 with (2^7) in H by reflexivity
  | [H: _ <= 256 |- _] => replace 256 with (2^8) in H by reflexivity
  | [H: _ > 2 |- _] => replace 2 with (2^1) in H by reflexivity
  | [H: _ > 4 |- _] => replace 4 with (2^2) in H by reflexivity
  | [H: _ > 8 |- _] => replace 8 with (2^3) in H by reflexivity
  | [H: _ > 16 |- _] => replace 16 with (2^4) in H by reflexivity
  | [H: _ > 32 |- _] => replace 32 with (2^5) in H by reflexivity
  | [H: _ > 64 |- _] => replace 64 with (2^6) in H by reflexivity
  | [H: _ > 128 |- _] => replace 128 with (2^7) in H by reflexivity
  | [H: _ > 256 |- _] => replace 256 with (2^8) in H by reflexivity
  | [H: _ >= 2 |- _] => replace 2 with (2^1) in H by reflexivity
  | [H: _ >= 4 |- _] => replace 4 with (2^2) in H by reflexivity
  | [H: _ >= 8 |- _] => replace 8 with (2^3) in H by reflexivity
  | [H: _ >= 16 |- _] => replace 16 with (2^4) in H by reflexivity
  | [H: _ >= 32 |- _] => replace 32 with (2^5) in H by reflexivity
  | [H: _ >= 64 |- _] => replace 64 with (2^6) in H by reflexivity
  | [H: _ >= 128 |- _] => replace 128 with (2^7) in H by reflexivity
  | [H: _ >= 256 |- _] => replace 256 with (2^8) in H by reflexivity
  end.

Ltac algify :=
  rewrite <-?mp2_shiftl_2_r, <-?mp2_shiftl_4_r, <-?mp2_shiftl_8_r,
          <-?mp2_shiftl_16_r, <-?mp2_shiftl_32_r, <-?mp2_shiftl_64_r,
          <-?mp2_shiftr_2, <-?mp2_shiftr_4, <-?mp2_shiftr_8,
          <-?mp2_shiftr_16, <-?mp2_shiftr_32, <-?mp2_shiftr_64,
          <-?mp2_mod_2, <-?mp2_mod_4, <-?mp2_mod_8, <-?mp2_mod_16,
          <-?mp2_mod_32, <-?mp2_mod_64, <-?mp2_mod_128, <-?mp2_mod_256
  in * |- *.


(* Beginning of asimpl, bsimpl, and csimpl. *)
Ltac2 Notation "thunkrw" rw(list1(rewriting, ",")) := fun () => rw.

Ltac2 asimpl_rw :=
  thunkrw ?N.add_0_r, ?N.add_0_l, ?N.sub_0_r, ?N.sub_0_l,
    ?N.sub_diag, ?N.mul_1_r, ?N.mul_1_l, ?N.div_1_r,
    ?N.pow_1_r, ?N.pow_0_r, ?N.pow_1_l,
    ?N.add_sub,
    ?N.ones_0, (* N.ones 0 = 0 *)
    ?N.div2_0, (* N.div2 0 = 0 *)
    ?N.pred_0, (* N.pred 0 = 0 *)
    ?N.ldiff_0_l, (* forall a : N, N.ldiff 0 a = 0 *)
    ?N.ldiff_diag, (* forall a : N, N.ldiff a a = 0 *)
    ?N.ldiff_0_r, (* forall a : N, N.ldiff a 0 = a *)
    ?N.lxor_0_l, (* forall a : N, N.lxor 0 a = a *)
    ?N.mod_0_r, (* forall a : N, a mod 0 = a *)
    ?N.lor_0_r, (* forall a : N, N.lor a 0 = a *)
    ?N.shiftr_0_l, (* forall n : N, 0 >> n = 0 *)
    ?N.lxor_0_r, (* forall a : N, N.lxor a 0 = a *)
    ?N.min_0_r, (* forall n : N, N.min n 0 = 0 *)
    ?N.land_0_r, (* forall a : N, N.land a 0 = 0 *)
    ?N.land_0_l, (* forall a : N, N.land 0 a = 0 *)
    ?N.div_0_r, (* forall a : N, a / 0 = 0 *)
    ?N.min_0_l, (* forall n : N, N.min 0 n = 0 *)
    ?N.lor_0_l, (* forall a : N, N.lor 0 a = a *)
    ?N.shiftl_0_l, (* forall n : N, 0 << n = 0 *)
    ?N.shiftr_0_r, (* forall a : N, a >> 0 = a *)
    ?N.max_0_l, (* forall n : N, N.max 0 n = n *)
    ?N.lxor_nilpotent, (* forall a : N, N.lxor a a = 0 *)
    ?N.Div0.mod_same, (* forall a : N, a mod a = 0 *)
    ?N.sub_diag, (* forall n : N, n - n = 0 *)
    ?N.shiftl_0_r, (* forall a : N, a << 0 = a *)
    ?N.max_0_r, (* forall n : N, N.max n 0 = n *)
    ?N.even_0, (* N.even 0 = true *)
    ?N.sub_0_r, (* forall n : N, n - 0 = n *)
    ?N.mul_0_r, (* forall n : N, n * 0 = 0 *)
    ?N.lcm_0_r, (* forall n : N, N.lcm n 0 = 0 *)
    ?N.sub_0_l, (* forall n : N, 0 - n = 0 *)
    ?N.add_0_r, (* forall n : N, n + 0 = n *)
    ?N.Div0.div_0_l, (* forall a : N, 0 / a = 0 *)
    ?N.odd_0, (* N.odd 0 = false *)
    ?N.mul_0_l, (* forall n : N, 0 * n = 0 *)
    ?N.Div0.mod_0_l, (* forall a : N, 0 mod a = 0 *)
    ?N.add_0_l, (* forall n : N, 0 + n = n *)
    ?msub_0, (* forall x y : N, msub 0 x y = 0 *)
    ?xbits_0_j, (* forall n i : N, xbits n i 0 = 0 *)
    ?xbits_0_l, (* forall i j : N, xbits 0 i j = 0 *)
    ?msub_diag, (* forall w x : N, msub w x x = 0 *)
    ?N.div2_1, (* N.div2 1 = 0 *)
    ?N.lnot_ones, (* forall n : N, N.lnot (N.ones n) n = 0 *)
    ?N.lnot_0_l, (* forall n : N, N.lnot 0 n = N.ones n *)
    ?N.bits_0, (* forall n : N, N.testbit 0 n = false *)
    ?N.Div0.mod_mul, (* forall a b : N, (a * b) mod b = 0 *)
    ?N.lor_eq_0_l, (* forall a b : N, N.lor a b = 0 -> a = 0 *)
    ?N.land_ldiff, (* forall a b : N, N.land (N.ldiff a b) b = 0 *)
    ?N.mod_1_r. (* forall a : N, a mod 1 = 0 *)

Ltac2 Notation "asimpl" := rewrite0 false (asimpl_rw ()) None None.
Ltac2 asimpl_in cl := rewrite0 false (asimpl_rw ()) (Some cl) None.

Tactic Notation "asimpl" := ltac2:(asimpl).
Tactic Notation "asimpl" "in" hyp(h) :=
  let f := ltac2:(h |-
    let i := Option.get (Ltac1.to_ident h) in
      asimpl_in {on_hyps := Some [(i,AllOccurrences,InHypTypeOnly)];
      on_concl :=NoOccurrences}
  ) in f h.
Tactic Notation "asimpl" "in" "*" :=
  ltac2:(asimpl_in {on_hyps:=None;on_concl:=AllOccurrences}).
(* Somehow this "*|-*" tactic notation breaks the Ltac csimpl definition. *)
(*Tactic Notation "asimpl" "in" "*|-*" :=*)
(*  ltac2:(asimpl_in {on_hyps:=None;on_concl:=AllOccurrences}).*)

Ltac2 bsimpl_rw :=
  thunkrw ?Bool.andb_false_r, ?Bool.andb_false_l,
          ?Bool.andb_true_r, ?Bool.andb_true_l,
          ?Bool.orb_false_r, ?Bool.orb_false_l,
          ?Bool.orb_true_r, ?Bool.orb_true_l,
          ?Nleb_add_l, ?Nleb_add_r,
          ?Nltb_add_l, ?Nltb_add_r,
          ?N.eqb_refl.
(* TODO: translate the comparison simplification and destruction to Ltac2. *)
(* TODO: Continue here adding a timeout variable and a notation for adding a timeout
   in lia_or_smt calls to help deving. *)
Ltac2 Notation "bsimpl" := rewrite0 false (bsimpl_rw ()) None None.
Ltac2 bsimpl_in cl := rewrite0 false (bsimpl_rw ()) (Some cl) None.

Tactic Notation "bsimpl" "in" hyp(h) :=
  let f := ltac2:(h|-
    let i := Option.get (Ltac1.to_ident h) in
      bsimpl_in {on_hyps:=Some [(i,AllOccurrences,InHypTypeOnly)];
                 on_concl:=NoOccurrences}
    ) in f h.

Ltac assert_true b := match b with true => idtac | _ => fail end.
Ltac assert_false b := match b with false => idtac | _ => fail end.

(* use_lia - true/false, enable/disable lia_or_smt invocations. *)
Ltac bsimpl0 use_lia lia_time :=
  ltac2:(bsimpl)
  || (assert_true use_lia; match goal with
      | |- context[?x=??y] => (replace (x=? y) with false by timeout lia_time lia_or_smt)
                          ||  (replace (x=? y) with true  by timeout lia_time lia_or_smt)
      | |- context[?x<??y] => (replace (x<? y) with false by timeout lia_time lia_or_smt)
                          ||  (replace (x<? y) with true  by timeout lia_time lia_or_smt)
      | |- context[?x<=??y]=> (replace (x<=?y) with false by timeout lia_time lia_or_smt)
                          ||  (replace (x<=?y) with true  by timeout lia_time lia_or_smt)
      end)
  || (match goal with
      | |- context[?x=??y] => let E := fresh "Eqn" in destruct (x=?y)  eqn:E
      | |- context[?x<??y] => let E := fresh "Eqn" in destruct (x<?y)  eqn:E
      | |- context[?x<=??y]=> let E := fresh "Eqn" in destruct (x<=?y) eqn:E
      end).
Ltac bsimpl := repeat bsimpl0 true ltac:(0).
Ltac simple_bsimpl := repeat bsimpl0 false ltac:(0).


Ltac csimpl:=
  rewrite ?N.ltb_lt, ?N.ltb_ge,
          ?N.leb_le, ?N.leb_gt,
          ?N.eqb_eq, ?N.eqb_neq in *|-*.

(** [specsimpl] reduces [N.testbit] expressions used in bit specification proofs.
    Most rewriting rules do not introduce new goals, but some do.  With some
    exceptions, we only use them if `lia` or the recursive solver,
    [solve bits inj] by default (below), solve the new goal.  This makes specsimpl
    recursive and introduces complexity, but the recursion is carefully managed
    by dispatching it only on goals of a predictable shape. *)
Ltac specsimpl_rec_solver := idtac.
(* Keep each lemma on a separate line to ease debugging.  If the aut-rewriting
   goes astray, find the offending lemma and either comment it out or relocate
   it. *)
Ltac specsimpl0 use_lia lia_time :=
  rewrite
  (* Picinae library theorems. *)
    ?N_ones_spec_ltb,
    ?testbit0_even,
    ?N_shiftl_spec_leb,
    ?Nshiftl_spec,
    ?signbit,
    ?xbits_spec,
    ?testbit_ofZ,
    (*?hibits_zero_bound,*)
    (*?bound_hibits_zero,*)
    ?cbits_spec,
    ?Nmod_pow2_bits,
    ?testbit_toZ,
    ?ashiftr_spec,
    ?rbits_spec,
    ?repbits_spec,
    ?popcount_bitmap,
    ?getbyte_spec,
    ?setbyte_spec,
    (*?logic_op_bound,*)
    ?revbytes_spec,
    ?swapbytes_spec,
    ?getmem_spec,
    ?setmem_spec,
    ?setmem_spec_anylen,
    ?Ntestbit_1,
    ?Nmod_pow2_bits_2,
    ?Nmod_pow2_bits_4,
    ?Nmod_pow2_bits_8,
    ?Nmod_pow2_bits_16,
    ?Nmod_pow2_bits_32,
    ?Nmod_pow2_bits_64,
    ?Nmod_pow2_bits_128,
    ?Nmod_pow2_bits_256,
(* From NArith *)
    ?N.bits_0, (* forall n : N, N.testbit 0 n = false *)
    ?N.clearbit_eq, (* forall a n : N, N.testbit (N.clearbit a n) n = false *)
    ?N.setbit_eq, (* forall a n : N, N.testbit (N.setbit a n) n = true *)
    ?N.testbit_div2, (* forall a n : N, N.testbit (N.div2 a) n = N.testbit a (N.succ n) *)
    ?N.shiftr_spec', (* forall a n m : N, N.testbit (a >> n) m = N.testbit a (m + n) *)
    ?N.lxor_spec, (* forall a a' n : N, N.testbit (a .^ a') n = xorb (N.testbit a n) (N.testbit a' n) *)
    ?N.land_spec, (* forall a a' n : N, N.testbit (a .& a') n = (N.testbit a n && N.testbit a' n)%bool *)
    ?N.lor_spec, (* forall a a' n : N, N.testbit (a .| a') n = (N.testbit a n || N.testbit a' n)%bool *)
    ?N.setbit_eqb, (* forall a n m : N, N.testbit (N.setbit a n) m = ((n =? m) || N.testbit a m)%bool *)
    ?N.pow2_bits_eqb, (* forall n m : N, N.testbit (2 ^ n) m = (n =? m) *)
    ?N.ldiff_spec, (* forall a a' n : N, N.testbit (N.ldiff a a') n = (N.testbit a n && negb (N.testbit a' n))%bool *)
    ?N.clearbit_eqb; (* forall a n m : N, N.testbit (N.clearbit a n) m = (N.testbit a m && negb (n =? m))%bool *)
    (* bits_above_pow2 is a powerful lemma, but needs extra care because
       it creates a new goal. *)
    try match goal with
    | H: ?x < 2 ^ ?w |- context[N.testbit ?x ?i] => assert_true use_lia;
      rewrite (bits_above_pow2 x i);[|apply N.lt_le_trans with (m:=2^w), N.pow_le_mono_r;algify;timeout lia_time lia_or_smt (*should be smt from coq-itauto*)]
    | |- _ => assert_true use_lia;
        rewrite Ntestbit_bound_cancel;[|algify; timeout lia_time lia_or_smt]
    | |- context[N.testbit (?x+?y) _] => rewrite <-(lor_plus x y);[|specsimpl_rec_solver]
    | |- context[N.testbit (?x-?y) _] => assert_true use_lia;
      rewrite <-(N.sub_nocarry_ldiff x y);[|specsimpl_rec_solver]
    | |- context[?x-?y+?y] => assert_true use_lia;
        rewrite N.sub_add;[|algify; timeout lia_time lia_or_smt]
    end.
Ltac specsimpl := specsimpl0 true ltac:(0).
Ltac simple_specsimpl := specsimpl0 false ltac:(0).

Ltac showgoal :=
  match goal with |- ?g => idtac g end.

(* sbi0 and sbi00 are useful for debugging and fine grained control if `solve bits inj`
   hangs on `smt`, which happens when bsimpl tries to infer conditions are `true` or `false
   with complex contexts. Note that sbi00 is not exactly an iteration of the inner loop 
   because it prevents bsimpl and asimpl from looping forever.  
   I.e., it interleaves specsimpl, asimpl0, and bsimpl0, whereas the real inner loop may
   get stuck in asimpl or bsimpl. *)
Ltac sbi00_lia    lia_time  := specsimpl0 true  lia_time  || asimpl || bsimpl0 true lia_time.
Ltac sbi00_simple           := specsimpl0 false ltac:(0)  || asimpl || bsimpl0 false ltac:(0).
Ltac sbi0_lia     lia_time  := specsimpl0 true  lia_time  || asimpl || bsimpl0 true lia_time.
Ltac sbi0_simple            := specsimpl0 false ltac:(0)  || asimpl || (repeat bsimpl0 false ltac:(0)).
Ltac solve_bits_inj use_lia lia_time :=
  (apply N.bits_inj_0 || apply N.bits_inj || idtac);
  let i := fresh "i" in try intro i;
  match use_lia with
  | true => repeat sbi0_lia lia_time
  | false => repeat sbi0_simple
  | _ => fail "solve_bits_inj invoked with bad argument: " use_lia "; expected 'true' or 'false'"
  end;
  (* Try to solve with `smt` if available, otherwise fall back to `lia`. *)
  match goal with
  | |- N.testbit _ _ = N.testbit _ _ => try reflexivity
  | |- context[N.testbit _ _] => idtac
  | |- _ => first [assert_true use_lia; algify; lia_or_smt
                  | assert_false use_lia
                  | idtac "'solve bits inj' undoing. Found goal it is stuck on:"; showgoal; fail]
  end.
Tactic Notation "solve" "bits" "inj" := solve_bits_inj (*use_lia=*)true ltac:(0).
Tactic Notation "solve" "bits" "inj" integer(i) := solve_bits_inj (*use_lia=*)true i.
Tactic Notation "simple" "solve" "bits" "inj" := solve_bits_inj (*use_lia=*)false.
Ltac specsimpl_rec_solver ::= solve bits inj.

End PicinaeAuto.
