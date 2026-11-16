(* 32-bit signed-comparison flags (SF, OF) as plain case analyses.

   GCC compiles signed comparisons to CMP + SETL/SETG/CMOVcc, which the lifter
   expresses through the sign bits of the operands and of their difference.
   s32_norm rewrites every such bit (x >> 31, slt 32 _ 0, toZ 32 _) of 32-bit
   values into boolean tests  x <? 2^31,  after which ctype_cases + lia finish.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common.
Open Scope N.

Lemma shr31: forall x, x < 2^32 -> x >> 31 = if x <? 2^31 then 0 else 1.
Proof.
  intros. rewrite N.shiftr_div_pow2. destruct (N.ltb_spec x (2^31)).
    apply N.div_small. assumption.
    change (2^31) with 2147483648 in *. change (2^32) with 4294967296 in *.
    apply N.le_antisymm.
      apply N.lt_succ_r. apply N.Div0.div_lt_upper_bound. lia.
      apply N.div_le_lower_bound. discriminate. lia.
Qed.

Lemma slt32_0': forall y, y < 2^32 -> slt 32 y 0 = negb (y <? 2^31).
Proof.
  intros y Y. rewrite slt32_0, testbit31_ge by assumption.
  destruct (N.leb_spec (2^31) y), (N.ltb_spec y (2^31)); reflexivity || lia.
Qed.

Lemma toZ32_cases:
  forall a, a < 2^32 -> toZ 32 a = if a <? 2^31 then Z.of_N a else (Z.of_N a - 2^32)%Z.
Proof.
  intros a A. unfold toZ, canonicalZ.
  change (Z.pred (Z.of_N 32)) with 31%Z. change (Z.of_N 32) with 32%Z.
  change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
  change (2^31) with 2147483648. change (2^32) with 4294967296 in A.
  destruct (N.ltb_spec a 2147483648); lia.
Qed.

Lemma shr0_mod32: forall x, x < 2^32 -> (x >> 0) mod 2^32 = x.
Proof. intros. rewrite N.shiftr_0_r. apply N.mod_small. assumption. Qed.

Ltac s32_norm a :=
  repeat first
  [ rewrite (shr0_mod32 a) in * by assumption
  | rewrite (shr31 a) in * by assumption
  | rewrite (toZ32_cases a) in * by assumption ].

Ltac s32_msub_norm :=
  repeat match goal with
  | |- context [msub 32 ?x ?y >> 31] => rewrite (shr31 (msub 32 x y)) by apply msub_lt
  | |- context [slt 32 (msub 32 ?x ?y) 0] => rewrite (slt32_0' (msub 32 x y)) by apply msub_lt
  | H: context [msub 32 ?x ?y >> 31] |- _ => rewrite (shr31 (msub 32 x y)) in H by apply msub_lt
  | H: context [slt 32 (msub 32 ?x ?y) 0] |- _ => rewrite (slt32_0' (msub 32 x y)) in H by apply msub_lt
  end.

(* Case on the innermost tests first, simplify constant flag arithmetic, and
   close by computation or lia. *)
Ltac flags_finish :=
  repeat (
    first
    [ match goal with |- context [if ?b then _ else _] =>
        lazymatch b with context [if _ then _ else _] => fail | _ =>
        lazymatch b with true => fail | false => fail | _ => destruct b eqn:? end end
      end
    | match goal with H: context [if ?b then _ else _] |- _ =>
        lazymatch b with context [if _ then _ else _] => fail | _ =>
        lazymatch b with true => fail | false => fail | _ => destruct b eqn:? end end
      end ];
    cbn [N.lxor N.land N.lor N.eqb negb Pos.lxor Pos.land Pos.lor Pos.eqb N.succ_double N.double Pos.Nsucc_double Pos.Ndouble] in *);
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end;
  first [ reflexivity
        | exfalso; unfold msub in *; change (2^32) with 4294967296 in *; change (2^31) with 2147483648 in *; lia ].

(* 64-bit: the sign bit as a test *)
Lemma shr63: forall x, x < 2^64 -> x >> 63 = if x <? 2^63 then 0 else 1.
Proof.
  intros. rewrite N.shiftr_div_pow2. destruct (N.ltb_spec x (2^63)).
    apply N.div_small. assumption.
    change (2^63) with 9223372036854775808 in *. change (2^64) with 18446744073709551616 in *.
    apply N.le_antisymm.
      apply N.lt_succ_r. apply N.Div0.div_lt_upper_bound. lia.
      apply N.div_le_lower_bound. discriminate. lia.
Qed.

(* CMP x,1; JG  (64-bit): the branch is taken iff x > 1 as a signed value.
   This is the condition exactly as psimpl leaves it after x64_step. *)
Lemma jg1_64:
  forall x, x < 2^64 ->
  (if (x >> 63 .^ msub 64 x 1 >> 63) .& (msub 64 x 1 >> 63 .^ 1) =?
      (if slt 64 (msub 64 x 1) 0 then 1 else 0)
   then if x =? 1 then 0 else 1 else 0)
  = (if (1 <? x) && (x <? 2^63) then 1 else 0).
Proof.
  intros x X. assert (Y: msub 64 x 1 < 2^64) by apply msub_lt.
  rewrite (shr63 x X), (shr63 _ Y), (slt64_0 _ Y).
  destruct (N.ltb_spec x (2^63)), (N.ltb_spec (msub 64 x 1) (2^63)),
           (N.eqb_spec x 1), (N.ltb_spec 1 x); simpl; try reflexivity;
  exfalso; unfold msub in *; change (2^64) with 18446744073709551616 in *;
  change (2^63) with 9223372036854775808 in *; lia.
Qed.
