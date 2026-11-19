(* Wide-search pointer reconstruction after the binary's signed length shift. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_wstrlen.
From Stdlib Require Import NArith Lia.
Open Scope N.

Lemma wide_length32_bytes:forall k,(4*wide_length32 k) mod 2^32=(4*k) mod 2^32.
Proof.
  intro k. unfold wide_length32.
  replace (4*k) with (N.shiftl k 2) by (rewrite N.shiftl_mul_pow2;lia).
  replace (4*ashiftr 32 (N.shiftl k 2 mod 2^32) 2) with
    (N.shiftl (ashiftr 32 (N.shiftl k 2 mod 2^32) 2) 2)
    by (rewrite N.shiftl_mul_pow2;lia).
  apply N.bits_inj. intro i. rewrite !Nmod_pow2_bits,!Nshiftl_spec.
  destruct (i<?32) eqn:B;cbn [andb];[|reflexivity].
  destruct (2<=?i) eqn:L;cbn [andb];[|reflexivity].
  pose proof (proj1 (N.ltb_lt _ _) B) as IB.
  pose proof (proj1 (N.leb_le _ _) L) as IL.
  rewrite ashiftr_spec. replace (i-2+2) with i by lia.
  rewrite N.min_l by lia. rewrite Nmod_pow2_bits,B,Nshiftl_spec,L.
  replace (i-2<?32) with true by (symmetry;apply N.ltb_lt;lia). reflexivity.
Qed.
Lemma wide_length32_address:forall p k,
  (p+4*wide_length32 k) mod 2^32=(p+4*k) mod 2^32.
Proof. intros. rewrite <- mp2_add_r at 1. rewrite wide_length32_bytes,mp2_add_r. reflexivity. Qed.
