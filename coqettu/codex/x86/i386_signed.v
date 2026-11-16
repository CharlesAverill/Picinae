(* Signed 32-bit subtraction flags, independent of concrete memory. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_bits.
From Stdlib Require Import NArith ZArith Lia.
Import X86Notations.
Open Scope N.

Lemma word32_signed_case : forall x, x < 2^32 ->
  toZ 32 x = if x <? 2^31 then Z.of_N x else (Z.of_N x-4294967296)%Z.
Proof.
  intros x X. destruct (x <? 2^31) eqn:SIGN; csimpl.
  - exact (toZ32_small x SIGN).
  - pose proof (proj1 (toZ_neg 32 x)) as T.
    rewrite (N.mod_small x (2^32) X) in T. exact (T SIGN).
Qed.

Lemma word32_sign_shift : forall x, x < 2^32 ->
  N.shiftr x 31 = if x <? 2^31 then 0 else 1.
Proof.
  intros x X. rewrite N.shiftr_div_pow2.
  destruct (x <? 2^31) eqn:SIGN; csimpl; lia.
Qed.

Definition sub_overflow32 (a b : N) : N :=
  N.land
    (N.lxor (N.shiftr a 31) (N.shiftr (msub 32 a b) 31))
    (N.lxor (N.lxor (N.shiftr (msub 32 a b) 31) (N.shiftr b 31)) 1).

Lemma sub_flags_signed_compare : forall a b,
  a < 2^32 -> b < 2^32 ->
  (sub_overflow32 a b =? (if slt 32 (msub 32 a b) 0 then 1 else 0)) =
  negb (slt 32 a b).
Proof.
  intros a b A B. set (d := msub 32 a b).
  assert (D : d < 2^32) by apply msub_lt.
  assert (REL : d = (a+4294967296-b) mod 4294967296).
  { unfold d, msub. rewrite (N.mod_small b (2^32) B).
    rewrite N.add_sub_assoc by lia. reflexivity. }
  unfold sub_overflow32. fold d.
  rewrite (word32_sign_shift a A), (word32_sign_shift b B), (word32_sign_shift d D).
  unfold slt. rewrite toZ_0_r.
  rewrite (word32_signed_case a A), (word32_signed_case b B), (word32_signed_case d D).
  clearbody d.
  destruct (a <? 2^31) eqn:SA;
    destruct (b <? 2^31) eqn:SB;
    destruct (d <? 2^31) eqn:SD;
    repeat match goal with |- context[Z.ltb ?x ?y] =>
      let E := fresh "CMP" in destruct (Z.ltb x y) eqn:E end;
    cbn [N.lxor N.land N.eqb negb]; try reflexivity;
    csimpl; rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.
