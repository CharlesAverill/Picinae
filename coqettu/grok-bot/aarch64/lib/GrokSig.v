(* Grok Bot (agent coqettu): small lemmas for musl's signal-set functions. *)
From Stdlib Require Import Utf8 NArith ZArith Lia.
Require Import Picinae_armv8.
Open Scope N.

Lemma msub32_1: ∀ d, msub 32 d 1 = if d mod 2^32 =? 0 then 2^32 - 1 else d mod 2^32 - 1.
Proof.
  intros. unfold msub. change (1 mod 2^32) with 1.
  rewrite <- mp2_add_l. pose proof (N.mod_lt d (2^32) ltac:(discriminate)).
  destruct (N.eqb_spec (d mod 2^32) 0) as [E|E].
  - rewrite E. reflexivity.
  - symmetry. apply N.mod_unique with (q := 1); lia.
Qed.

Lemma msub6_32: ∀ d, msub 6 d 1 = msub 32 d 1 mod 2^6.
Proof.
  intros. unfold msub. change (1 mod 2^32) with 1. change (1 mod 2^6) with 1.
  change (2^32) with (2^(6+26)). rewrite (mp2_mod_mul_r _ 6 26).
  rewrite N.mul_comm, N.Div0.mod_add, N.Div0.mod_mod.
  replace (d + (2^(6+26) - 1)) with (d + (2^6 - 1) + 67108863 * 2^6) by (cbn; lia).
  rewrite N.Div0.mod_add. reflexivity.
Qed.
